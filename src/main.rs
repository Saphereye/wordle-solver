use eframe::egui;
use egui::{Color32, Sense, Stroke, Vec2};
use std::collections::HashMap;
use std::sync::mpsc;
use std::thread;
use std::time::{Duration, Instant};

const ROWS: usize = 6;
const COLS: usize = 5;

#[derive(Clone, Copy, PartialEq, Eq)]
enum TileState {
    Unknown,
    Yellow,
    Green,
}

impl TileState {
    fn cycle(self) -> Self {
        match self {
            TileState::Unknown => TileState::Yellow,
            TileState::Yellow => TileState::Green,
            TileState::Green => TileState::Unknown,
        }
    }

    fn color(self) -> Color32 {
        match self {
            TileState::Unknown => Color32::from_rgb(120, 124, 126),
            TileState::Yellow => Color32::from_rgb(201, 180, 88),
            TileState::Green => Color32::from_rgb(106, 170, 100),
        }
    }

    fn text_color(self) -> Color32 {
        match self {
            TileState::Unknown => Color32::WHITE,
            TileState::Yellow => Color32::BLACK,
            TileState::Green => Color32::WHITE,
        }
    }
}

struct WordleApp {
    grid: [[String; COLS]; ROWS],
    states: [[TileState; COLS]; ROWS],
    active_row: usize,
    focused_cell: Option<(usize, usize)>,
    word_list: Vec<String>,
    candidates: Vec<String>,
    suggestions: Vec<(String, f64, f64)>,
    use_full_guess_list: bool,
    suggestion_req_tx: mpsc::Sender<(Vec<String>, Vec<String>, bool)>,
    suggestion_res_rx: mpsc::Receiver<Vec<(String, f64, f64)>>,
    loaded_count: usize,
    auto_filled_row: Option<usize>,
    last_input_time: Option<std::time::Instant>,
    pending_recompute: bool,
    debounce_ms: u64,
}

impl WordleApp {
    fn new_with_words(
        words: Vec<String>,
        suggestion_req_tx: mpsc::Sender<(Vec<String>, Vec<String>, bool)>,
        suggestion_res_rx: mpsc::Receiver<Vec<(String, f64, f64)>>,
    ) -> Self {
        let initial_candidates = words.clone();
        let loaded_count = initial_candidates.len();
        Self {
            grid: array_init::array_init(|_| array_init::array_init(|_| String::new())),
            states: array_init::array_init(|_| array_init::array_init(|_| TileState::Unknown)),
            active_row: 0,
            focused_cell: None,
            word_list: words,
            candidates: initial_candidates,
            suggestions: Vec::new(),
            use_full_guess_list: false,
            suggestion_req_tx,
            suggestion_res_rx,
            loaded_count,
            auto_filled_row: None,
            last_input_time: None,
            pending_recompute: false,
            debounce_ms: 200,
        }
    }

    fn recompute_candidates(&mut self) {
        #[derive(Default)]
        struct GuessInfo {
            guess: Vec<char>,      // '.' for empty
            state: Vec<TileState>, // same len
        }

        let mut guesses: Vec<GuessInfo> = Vec::new();
        for r in 0..ROWS {
            let mut any = false;
            let mut g = Vec::with_capacity(COLS);
            let mut s = Vec::with_capacity(COLS);
            let mut all_states_unknown = true;
            for c in 0..COLS {
                let cell = &self.grid[r][c];
                if !cell.is_empty() {
                    any = true;
                    g.push(cell.chars().next().unwrap());
                } else {
                    g.push('.');
                }
                let st = self.states[r][c];
                if st != TileState::Unknown {
                    all_states_unknown = false;
                }
                s.push(st);
            }
            if any {
                // If this row was auto-filled at startup and the user hasn't colored any tile yet,
                // skip treating it as an actual guess (so it won't constrain candidates prematurely).
                if let Some(afr) = self.auto_filled_row {
                    if afr != r || !all_states_unknown {
                        guesses.push(GuessInfo { guess: g, state: s });
                    }
                } else {
                    guesses.push(GuessInfo { guess: g, state: s });
                }
            }
        }

        // If no guesses, all words are candidates
        if guesses.is_empty() {
            self.candidates = self.word_list.clone();
            return;
        }

        // Build constraints
        let mut min_required: HashMap<char, usize> = HashMap::new();
        let mut max_allowed: HashMap<char, usize> = HashMap::new();
        let mut banned_letters: HashMap<char, bool> = HashMap::new();

        let mut must_be: [Option<char>; COLS] = [None, None, None, None, None];
        let mut cannot_be_pos: [Vec<char>; COLS] =
            [Vec::new(), Vec::new(), Vec::new(), Vec::new(), Vec::new()];

        for guess in &guesses {
            let mut total_counts: HashMap<char, usize> = HashMap::new();
            let mut good_counts: HashMap<char, usize> = HashMap::new();
            for (i, &ch) in guess.guess.iter().enumerate() {
                if ch == '.' {
                    continue;
                }
                *total_counts.entry(ch).or_insert(0) += 1;
                if guess.state[i] == TileState::Green || guess.state[i] == TileState::Yellow {
                    *good_counts.entry(ch).or_insert(0) += 1;
                }
            }

            for (i, &ch) in guess.guess.iter().enumerate() {
                if ch == '.' {
                    continue;
                }
                match guess.state[i] {
                    TileState::Green => {
                        must_be[i] = Some(ch);
                    }
                    TileState::Yellow => {
                        cannot_be_pos[i].push(ch);
                    }
                    TileState::Unknown => { /* gray */ }
                }
            }

            for (&ch, &tot) in total_counts.iter() {
                let good = *good_counts.get(&ch).unwrap_or(&0usize);
                if good == 0 && tot > 0 {
                    // only gray occurrences -> banned
                    banned_letters.insert(ch, true);
                    let entry = max_allowed.entry(ch).or_insert(usize::MAX);
                    *entry = (*entry).min(0);
                } else {
                    let entry = min_required.entry(ch).or_insert(0);
                    *entry = (*entry).max(good);
                    if tot > good {
                        // some grays as well, so this guess implies max = good
                        let entry = max_allowed.entry(ch).or_insert(usize::MAX);
                        *entry = (*entry).min(good);
                    }
                }
            }
        }

        let mut out: Vec<String> = Vec::new();
        'word_loop: for w in &self.word_list {
            let word = w.as_bytes();
            if word.len() != COLS {
                continue;
            }

            // position constraints
            for i in 0..COLS {
                if let Some(ch) = must_be[i]
                    && word[i] as char != ch
                {
                    continue 'word_loop;
                }
                for &forbidden in &cannot_be_pos[i] {
                    if word[i] as char == forbidden {
                        continue 'word_loop;
                    }
                }
            }

            // counts
            let mut cand_counts: HashMap<char, usize> = HashMap::new();
            for i in word.iter().take(COLS) {
                let ch = i;
                *cand_counts.entry(*ch as char).or_insert(0) += 1;
            }

            for (&banned, _) in banned_letters.iter() {
                if *cand_counts.get(&banned).unwrap_or(&0usize) > 0 {
                    continue 'word_loop;
                }
            }

            for (&ch, &minreq) in min_required.iter() {
                let have = *cand_counts.get(&ch).unwrap_or(&0usize);
                if have < minreq {
                    continue 'word_loop;
                }
            }

            for (&ch, &maxa) in max_allowed.iter() {
                if maxa == usize::MAX {
                    continue;
                }
                let have = *cand_counts.get(&ch).unwrap_or(&0usize);
                if have > maxa {
                    continue 'word_loop;
                }
            }

            // per-guess yellow sanity check
            for guess in &guesses {
                for i in 0..COLS {
                    let ch = guess.guess[i];
                    if ch == '.' {
                        continue;
                    }
                    if guess.state[i] == TileState::Yellow {
                        let mut found = false;
                        for (j, &char) in word.iter().enumerate().take(COLS) {
                            if j == i {
                                continue;
                            }
                            if char as char == ch {
                                found = true;
                                break;
                            }
                        }
                        if !found {
                            continue 'word_loop;
                        }
                    }
                }
            }

            out.push(w.clone());
        }

        out.sort();
        self.candidates = out;
        // request background suggestion computation
        let _ = self.suggestion_req_tx.send((
            self.word_list.clone(),
            self.candidates.clone(),
            self.use_full_guess_list,
        ));
    }
}

impl Default for WordleApp {
    fn default() -> Self {
        let fallback = embedded_fallback_words();
        let (req_tx, req_rx) = mpsc::channel::<(Vec<String>, Vec<String>, bool)>();
        let (res_tx, res_rx) = mpsc::channel::<Vec<(String, f64, f64)>>();
        std::thread::spawn(move || {
            while let Ok((_wl, _cand, _use_full)) = req_rx.recv() {
                // return empty vector quickly
                let _ = res_tx.send(Vec::new());
            }
        });
        WordleApp::new_with_words(fallback, req_tx, res_rx)
    }
}

impl eframe::App for WordleApp {
    fn update(&mut self, ctx: &egui::Context, _frame: &mut eframe::Frame) {
        use egui::ScrollArea;

        if let Ok(s) = self.suggestion_res_rx.try_recv() {
            self.suggestions = s;
        }

        let events = ctx.input(|i| i.events.clone());
        for ev in events {
            match ev {
                egui::Event::Text(s) => {
                    if !s.is_empty() {
                        let ch = s.chars().next().unwrap();
                        if ch.is_ascii_alphabetic() {
                            // If a cell is focused, write there and advance focus to next column.
                            if let Some((r, c)) = self.focused_cell {
                                self.grid[r][c] = ch.to_ascii_lowercase().to_string();
                                // advance focus
                                let next_c = if c + 1 < COLS { c + 1 } else { COLS - 1 };
                                self.focused_cell = Some((r, next_c));
                                self.active_row = r;
                                self.last_input_time = Some(Instant::now());
                                self.pending_recompute = true;
                            } else {
                                // No focused cell: put in first empty cell of active row (or overwrite last)
                                let ar = self.active_row;
                                let mut placed = false;
                                for cc in 0..COLS {
                                    if self.grid[ar][cc].is_empty() {
                                        self.grid[ar][cc] = ch.to_ascii_lowercase().to_string();
                                        self.focused_cell = Some((ar, cc));
                                        self.last_input_time = Some(Instant::now());
                                        self.pending_recompute = true;
                                        placed = true;
                                        break;
                                    }
                                }
                                if !placed {
                                    self.grid[ar][COLS - 1] = ch.to_ascii_lowercase().to_string();
                                    self.focused_cell = Some((ar, COLS - 1));
                                    self.last_input_time = Some(Instant::now());
                                    self.pending_recompute = true;
                                }
                            }
                        }
                    }
                }
                egui::Event::Key { key, pressed, .. } => {
                    // Backspace: clear focused cell or last letter in active row.
                    if key == egui::Key::Backspace && pressed {
                        if let Some((r, c)) = self.focused_cell {
                            self.grid[r][c].clear();
                            self.last_input_time = Some(Instant::now());
                            self.pending_recompute = true;
                        } else {
                            let ar = self.active_row;
                            for cc in (0..COLS).rev() {
                                if !self.grid[ar][cc].is_empty() {
                                    self.grid[ar][cc].clear();
                                    self.focused_cell = Some((ar, cc));
                                    self.last_input_time = Some(Instant::now());
                                    self.pending_recompute = true;
                                    break;
                                }
                            }
                        }
                    }
                    // Enter: advance active row
                    if key == egui::Key::Enter && pressed {
                        self.active_row = (self.active_row + 1).min(ROWS - 1);
                        self.focused_cell = None;
                    }

                    // Arrow navigation
                    if key == egui::Key::ArrowRight
                        && pressed
                        && let Some((r, c)) = self.focused_cell
                    {
                        let nc = (c + 1).min(COLS - 1);
                        self.focused_cell = Some((r, nc));
                        self.active_row = r;
                    }

                    if key == egui::Key::ArrowLeft
                        && pressed
                        && let Some((r, c)) = self.focused_cell
                    {
                        let nc = c.saturating_sub(1);
                        self.focused_cell = Some((r, nc));
                        self.active_row = r;
                    }
                }
                _ => {}
            }
        }

        // Debounce logic: perform recompute if pending and user has been idle long enough.
        if self.pending_recompute
            && let Some(ts) = self.last_input_time
            && ts.elapsed() >= std::time::Duration::from_millis(self.debounce_ms)
        {
            self.recompute_candidates();
            self.pending_recompute = false;
        }

        // --- Top panel ---
        egui::TopBottomPanel::top("top").show(ctx, |ui| {
            ui.horizontal(|ui| {
                ui.vertical(|ui| {
                    ui.label("Lightweight Wordle solver");
                    ui.label("Type letters to fill the active row; Backspace deletes; Enter advances row.");
                });
                if ui.button("Clear All").clicked() {
                    for r in 0..ROWS {
                        for c in 0..COLS {
                            self.grid[r][c].clear();
                            self.states[r][c] = TileState::Unknown;
                        }
                    }
                    self.focused_cell = None;
                    self.active_row = 0;
                    self.candidates = self.word_list.clone();
                }
                if let Some((best, _info, _exp)) = self.suggestions.first() {
                    ui.label(format!("Top suggestion: {}", best));
                }
            });
        });

        // --- Side panel: show top suggestions (by info gain) then candidates ---
        egui::SidePanel::right("side")
            .min_width(260.0)
            .show(ctx, |ui| {
                ui.heading("Suggestions (information gain)");
                ui.separator();
                ui.checkbox(&mut self.use_full_guess_list, "Use full word list for suggestions (slower)");
                ui.label(format!("Loaded: {} words", self.loaded_count));
                let top_n = 12usize;
                if self.suggestions.is_empty() {
                    ui.label("No suggestions yet.");
                } else {
                    for (i, (guess, info, expected)) in self.suggestions.iter().take(top_n).enumerate() {
                        ui.horizontal(|ui| {
                            ui.monospace(format!("{:2}. {}", i + 1, guess));
                            ui.add_space(6.0);
                            ui.label(format!("gain: {:.2}", info));
                            ui.add_space(6.0);
                            ui.label(format!("exp_remain: {:.1}", expected));
                        });
                    }
                }
                ui.add_space(6.0);
                ui.separator();
                ui.label(format!("Matching candidates: {}", self.candidates.len()));
                ui.add_space(4.0);
                ScrollArea::vertical().show(ui, |ui| {
                    for w in &self.candidates {
                        ui.monospace(w);
                    }
                });
                ui.add_space(8.0);
                if ui.button("Recompute").clicked() {
                    self.recompute_candidates();
                }
                ui.add_space(6.0);
                if ui.button("Reload words.txt").clicked() {
                    let words = get_words_list();
                    self.word_list = words;
                    self.candidates = self.word_list.clone();
                    self.loaded_count = self.word_list.len();
                    self.recompute_candidates();
                }
                ui.add_space(6.0);
                ui.label("Tip: Type directly to fill the active row; left-click to focus a tile; right-click to cycle colors.");
            });

        // --- Center: draw grid and allow click interactions ---
        egui::CentralPanel::default().show(ctx, |ui| {
            ui.vertical_centered(|ui| {
                ui.add_space(6.0);
                for r in 0..ROWS {
                    ui.horizontal(|ui| {
                        for c in 0..COLS {
                            let size = Vec2::new(52.0, 52.0);
                            let (rect, response) = ui.allocate_exact_size(size, Sense::click());
                            let bg = self.states[r][c].color();
                            ui.painter().rect_filled(rect, 6.0, bg);
                            // highlight focused cell with a white thicker border
                            if self.focused_cell == Some((r, c)) {
                                ui.painter().rect_stroke(rect, 6.0, Stroke::new(3.0, Color32::WHITE));
                            } else {
                                ui.painter().rect_stroke(rect, 6.0, Stroke::new(1.0, Color32::BLACK));
                            }
                            let letter = if self.grid[r][c].is_empty() {
                                " ".to_owned()
                            } else {
                                self.grid[r][c].to_uppercase()
                            };
                            ui.painter().text(
                                rect.center(),
                                egui::Align2::CENTER_CENTER,
                                letter,
                                egui::FontId::proportional(28.0),
                                self.states[r][c].text_color(),
                            );

                            // Global keyboard input is handled above; no per-cell overlay TextEdit is used.
                            // (Typing will insert into the focused cell or the active row.)

                            if response.clicked() {
                                // left-click: focus this tile (do not change color)
                                self.focused_cell = Some((r, c));
                                self.active_row = r;
                            }
                            if response.secondary_clicked() {
                                // right-click: cycle color and recompute
                                self.states[r][c] = self.states[r][c].cycle();
                                self.recompute_candidates();
                            }
                            if response.double_clicked() {
                                // clear tile on double-click
                                self.grid[r][c].clear();
                                self.states[r][c] = TileState::Unknown;
                                self.focused_cell = Some((r, c));
                                self.recompute_candidates();
                            }
                            ui.add_space(6.0);
                        }
                    });
                    ui.add_space(8.0);
                }

                ui.separator();
                ui.add_space(6.0);
                // Small editor controls for focused cell (input entered via keyboard events above)
                if let Some((fr, fc)) = self.focused_cell {
                    ui.horizontal(|ui| {
                        ui.label(format!("Editing row {}, col {}", fr + 1, fc + 1));
                        if ui.button("Clear").clicked() {
                            self.grid[fr][fc].clear();
                            self.states[fr][fc] = TileState::Unknown;
                            self.pending_recompute = true;
                            self.last_input_time = Some(Instant::now());
                        }
                        if ui.button("Unset Focus").clicked() {
                            self.focused_cell = None;
                        }
                    });
                } else {
                    ui.label("Type letters to fill the active row; click a tile to focus. Backspace deletes; Enter advances row.");
                }
            });
        });

        ctx.request_repaint_after(std::time::Duration::from_millis(200));
    }
}

fn get_words_list() -> Vec<String> {
    let text = include_str!("../words.txt");
    let mut words = Vec::new();
    for line in text.lines() {
        let w = line.trim();
        if w.len() == COLS && w.chars().all(|ch| ch.is_ascii_alphabetic()) {
            words.push(w.to_ascii_lowercase());
        }
    }
    words
}

fn main() {
    // Try runtime load, fall back to embedded words.
    let words = get_words_list();

    // Create suggestion channels and spawn background worker that computes ranked suggestions.
    let (req_tx, req_rx) = mpsc::channel::<(Vec<String>, Vec<String>, bool)>();
    let (res_tx, res_rx) = mpsc::channel::<Vec<(String, f64, f64)>>();
    // Background worker: computes information-gain suggestions and sends results back.
    thread::spawn(move || {
        while let Ok(req) = req_rx.recv() {
            let (word_list, candidates, use_full) = req;
            let targets: Vec<String> = candidates.clone();
            let total = targets.len() as f64;
            let mut out: Vec<(String, f64, f64)> = Vec::new();
            if total > 0.0 {
                // choose guess source
                let guess_source = if use_full {
                    word_list.clone()
                } else {
                    candidates.clone()
                };
                for g in guess_source.iter() {
                    let mut counts: std::collections::HashMap<usize, usize> =
                        std::collections::HashMap::new();
                    for t in targets.iter() {
                        // compute feedback pattern between g and t
                        let gchars: Vec<char> = g.chars().collect();
                        let mut tchars: Vec<char> = t.chars().collect();
                        let mut state = [0u8; 5];
                        // greens
                        for i in 0..5 {
                            if gchars[i] == tchars[i] {
                                state[i] = 2;
                                tchars[i] = '*';
                            }
                        }
                        // yellows
                        for i in 0..state.len() {
                            if state[i] == 0 {
                                for j in tchars.iter_mut() {
                                    if *j == gchars[i] {
                                        state[i] = 1;
                                        *j = '*';
                                        break;
                                    }
                                }
                            }
                        }
                        // encode base-3
                        let mut code = 0usize;
                        for i in state {
                            code = code * 3 + (i as usize);
                        }
                        *counts.entry(code).or_insert(0) += 1;
                    }
                    // expected remaining = sum(count^2) / total
                    let mut sum_sq: f64 = 0.0;
                    for &c in counts.values() {
                        sum_sq += (c as f64) * (c as f64);
                    }
                    let expected_remaining = sum_sq / total;
                    let info_gain = total - expected_remaining;
                    out.push((g.clone(), info_gain, expected_remaining));
                }
                // sort by info gain descending
                out.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap_or(std::cmp::Ordering::Equal));
            }
            // send results (best-effort)
            let _ = res_tx.send(out);
            // small pause to yield (prevents hot-loop if multiple requests arrive quickly)
            std::thread::sleep(Duration::from_millis(10));
        }
    });
    let mut app = WordleApp::new_with_words(words, req_tx, res_rx);
    // Apply an initial guess into the first row (prefer "crane" if available, else first word).
    if !app.word_list.is_empty() {
        let initial = if app.word_list.iter().any(|w| w == "crane") {
            "crane".to_string()
        } else {
            app.word_list[0].clone()
        };
        for (i, ch) in initial.chars().enumerate().take(COLS) {
            app.grid[0][i] = ch.to_string();
            // keep states Unknown until user marks them (so recompute skips this row)
            app.states[0][i] = TileState::Unknown;
        }
        app.auto_filled_row = Some(0);
    }
    // initial compute (in case embedded list differs)
    app.recompute_candidates();

    let options = eframe::NativeOptions {
        initial_window_size: Some(egui::vec2(920.0, 560.0)),
        ..Default::default()
    };

    eframe::run_native(
        "Wordle Solver (egui)",
        options,
        Box::new(|_cc| Box::new(app)),
    )
    .expect("failed to start eframe");
}

/// Small fallback list used when no words.txt is found.
/// Keep this small so the binary remains lightweight.
fn embedded_fallback_words() -> Vec<String> {
    vec![
        "crane", "slate", "adieu", "raise", "soare", "trend", "gripe", "plant", "bench", "crown",
        "flint", "sugar", "model", "table", "whack", "about", "other", "which", "their", "there",
        "apple", "grape", "berry", "chair", "smile", "light", "night", "sound", "water", "mouse",
        "house", "heart", "earth", "money", "pride", "small", "large", "young", "train", "plane",
        "brain", "spark", "stone", "river", "ocean", "paint", "press", "hello", "smart", "index",
        "group", "debug", "rusty", "cargo", "build", "watch", "focus", "world", "brick", "flame",
        "sheep", "ghost", "sugar", "spice", "frame", "trend", "alert", "bench", "candy", "dwell",
        "eager", "fancy", "mango", "nerve", "piano", "queen", "rival", "tempo", "urban", "vivid",
        "witty", "youth", "zesty",
    ]
    .into_iter()
    .map(|s| s.to_string())
    .collect()
}
