use std::cmp::Reverse;
use std::collections::{
    HashMap, HashSet, hash_map::DefaultHasher,
};
use std::hash::{Hash, Hasher};
type Uid = u16;

struct List(Vec<[Uid; 2]>); //{{{
impl List {
    fn new(n: usize) -> Self {
        let mut list = Vec::with_capacity(n + 1);
        let n = n as Uid;
        list.push([n, 1]);
        list.extend((0 .. n - 1).map(|j| [j, j + 2]));
        list.push([n - 1, 0]);
        Self(list)
    }
    fn iter(&self) -> ListIter {
        let n = self.0.len() - 1;
        ListIter {
            list: &self.0[.. n],
            index: self.0[n][1] as usize,
        }
    }
    fn remove(&mut self, index: usize) {
        let [p, n] = self.0[index];
        self.0[p as usize][1] = n;
        self.0[n as usize][0] = p;
    }
    fn restore(&mut self, index: usize) {
        let [p, n] = self.0[index];
        let i = index as Uid;
        self.0[p as usize][1] = i;
        self.0[n as usize][0] = i;
    }
}

struct ListIter<'a> {
    list: &'a [[Uid; 2]],
    index: usize,
}
impl<'a> Iterator for ListIter<'a> {
    type Item = usize;
    fn next(&mut self) -> Option<Self::Item> {
        let mut index = self.list.get(self.index)?[1] as usize;
        std::mem::swap(&mut self.index, &mut index);
        Some(index)
    }
}
//}}}
struct Bottle<const N: usize> { //{{{
    air: Uid,
    len: Uid,
    data: [(Uid, Uid); N],
}
impl<const N: usize> Bottle<N> {
    fn new(bottle: &[Uid; N]) -> Self {
        let (mut data, mut len) = ([(0, 0); N], 0);
        let (mut last, mut cnt) = (0, 0);
        for &x in bottle.iter().rev().chain(std::iter::once(&0)) {
            if x != last {
                if last != 0 {
                    data[len as usize] = (last, cnt);
                    len += 1;
                }
                last = x; cnt = 0;
            }
            cnt += 1;
        }
        Self { air: cnt - 1, len, data }
    }
    #[inline] fn is_full(&self) -> bool {
        self.air == 0 && self.len == 1
    }
    #[inline] fn is_empty(&self) -> bool {
        self.len == 0
    }
}
//}}}
struct Puzzle<const N: usize> { //{{{
    count: usize,
    board: Vec<Bottle<N>>,
    list: List,
}
impl<const N: usize> Puzzle<N> {
    fn new(count: usize, board: Vec<[Uid; N]>) -> Self {
        let mut list = List::new(board.len());
        let board = board.iter().enumerate().map(|(j, arr)| {
            let bottle = Bottle::new(arr);
            if bottle.is_full() { list.remove(j); }
            bottle
        }).collect();
        Self { count, board, list }
    }
    fn is_done(&self) -> bool {
        self.list.iter().all(|j| self.board[j].is_empty())
    }
    fn get_kind(&self) -> Vec<Vec<(Uid, Uid, Uid)>> {
        let mut ret = vec![vec![]; self.count];
        for j in self.list.iter() {
            if self.board[j].is_empty() {
                ret[0].push((j as Uid, N as Uid, 0));
                continue;
            }
            let bottle = &self.board[j];
            let (kind, cnt) = bottle.data[bottle.len as usize - 1];
            ret[kind as usize].push((j as Uid, bottle.air, cnt));
        }
        ret
    }
    fn pour(&mut self, src: usize, dst: usize, len: Uid) {
        let len = len as Uid;
        let src = &mut self.board[src]; src.air += len;
        let (kind, ref mut l) = src.data[src.len as usize - 1];
        if *l == len { src.len -= 1; } else { *l -= len; }
        let dst = &mut self.board[dst]; dst.air -= len;
        let ind = dst.len as usize;
        if dst.is_empty() || dst.data[ind - 1].0 != kind {
            dst.data[ind] = (kind, len); dst.len += 1;
        } else { dst.data[ind - 1].1 += len; }
    }
    fn hash(&self) -> u64 {
        let mut s = DefaultHasher::new();
        for bottle in &self.board {
            bottle.data[.. bottle.len as usize].hash(&mut s);
        }
        s.finish()
    }
}
//}}}

fn wp_check<const N: usize>(board: &Vec<[&str; N]>) -> bool { //{{{
    let mut record = HashMap::new();
    for &s in board.iter().flatten() {
        record.entry(s).and_modify(|c| *c += 1).or_insert(1);
    }
    record.into_values().all(|c| c % (N as Uid) == 0) && {
        for v in board {
            let Some(pos) = v.iter().rposition(|&s| s == "")
                else { continue; };
            if !v[.. pos].iter().all(|&s| s == "") {
                return false;
            }
        }
        true
    }
}
//}}}
fn wp_solve<const N: usize>(board: &Vec<[&str; N]>) -> Vec<(usize, usize)> { //{{{
    #[cfg(debug_assertions)]
    let mut count = 0;
    let mut puzzle = { //{{{
        let mut record = HashMap::from([("", 0)]);
        let mut cnt = 0;
        for &s in board.iter().flatten() {
            record.entry(s).or_insert_with(|| { cnt += 1; cnt });
        }
        Puzzle::new(
            cnt as usize + 1,
            board.iter().map(|&v| v.map(|s| record[&s])).collect(),
        )
    };
    //}}}
    let (mut stack, mut buffer) = (vec![], vec![]);
    let mut ext_table = vec![vec![]; puzzle.board.len()];
    let mut fail_state = HashSet::new();
    'L: loop {
        //{{{ Prelude
        macro_rules! apply { //{{{
            ($op: expr) => {{
                let (src, dst, len) = $op;
                let (src, dst) = (src as usize, dst as usize);
                puzzle.pour(src, dst, len);
                if puzzle.board[dst].is_full() {
                    puzzle.list.remove(dst);
                }
            }};
        }
        //}}}
        macro_rules! undo { //{{{
            ($op: expr) => {{
                let (src, dst, len) = $op;
                let (src, dst) = (src as usize, dst as usize);
                if puzzle.board[dst].is_full() {
                    puzzle.list.restore(dst);
                }
                puzzle.pour(dst, src, len);
            }};
        }
        //}}}
        macro_rules! save { //{{{
            (|$i: ident| $body: block) => {{
                if !buffer.is_empty() {
                    let mut indices = (0 .. buffer.len()).collect::<Vec<_>>();
                    indices.sort_unstable_by_key(|&i| buffer[i].0);
                    for $i in indices $body;
                    buffer.clear();
                }
            }};
        }
        //}}}
        let level = if let Some(&(op, level)) = stack.last() { 'S: {
            apply!(op); if level != 0 { break 'S level + 1; }
            for &(op, level) in stack.iter().rev().skip(1) {
                apply!(op); if level != 0 { break 'S level + 1; }
            }
            unreachable!()
        }} else { 1 as Uid };
        //}}}
        if !fail_state.contains(&puzzle.hash()) {
            //{{{ Backtrack
            if puzzle.is_done() {
                #[cfg(debug_assertions)]
                eprintln!("[DBG] \x1b[33m#fail_state = {}\x1b[m", fail_state.len());
                let (mut ret, mut buffer, mut last) = (vec![], vec![], Uid::MAX);
                for &((src, dst, _), level) in stack.iter().rev() {
                    if level == 0 {
                        buffer.push((src as usize, dst as usize));
                        continue;
                    }
                    if level == last {
                        buffer.clear();
                        continue;
                    }
                    last = level;
                    ret.push((src as usize, dst as usize));
                    ret.extend(buffer.drain(..).rev());
                }
                ret.reverse();
                return ret;
            }
            //}}}
            //{{{ Extend stack
            let mut kind = puzzle.get_kind();
            if !kind[0].is_empty() {
                let nil = kind[0][0].0;
                for v in &kind[1 ..] {
                    for &(j, c1, c2) in v {
                        if c1 + c2 < N as Uid {
                            buffer.push(((c2, c1, Reverse(j)), (j, nil, c2)));
                        }
                    }
                }
                save!(|i| { stack.push((buffer[i].1, level)); });
            }
            for v in &mut kind[1 ..] {
                v.sort_unstable_by_key(|&(_, air, _)| Reverse(air));
                let c = v.iter().map(|&(_, air, _)| air).sum::<Uid>();
                for &(j, c1, c2) in v.iter() {
                    if c1 + c2 > c { continue; }
                    let (mut acc, mut m) = (0, 0);
                    for &(i, air, cnt) in v.iter() {
                        if i == j { continue; }
                        acc += air; m = m.max(air + cnt);
                        if acc >= c2 {
                            buffer.push(((m, c2, Reverse(j)), (j, i, c2 - (acc - air))));
                            break;
                        }
                        ext_table[j as usize].push((i, air));
                    }
                }
            }
            save!(|i| {
                let ((_, c_, _), (j, i, c)) = buffer[i];
                stack.push(((j, i, c), level));
                if c != c_ {
                    for (i, air) in ext_table[j as usize].drain(..).rev() {
                        stack.push(((j, i, air), 0));
                    }
                }
            });
            #[cfg(debug_assertions)]
            {
                eprint!("[DBG] \x1b[34mstack = ");
                if stack.len() > 5 {
                    eprint!("[...");
                    for op in &stack[stack.len() - 5 ..] {
                        eprint!(", {:?}", op);
                    }
                    eprint!("]");
                } else { eprint!("{:?}", stack); }
                eprintln!("\x1b[m");
            }
            //}}}
        } else {
            #[cfg(debug_assertions)]
            eprintln!("[DBG] \x1b[33mHit fail_state\x1b[m");
        }
        //{{{ Rewind stack
        let mut last = level;
        while let Some(&(op, level)) = stack.last() {
            if level == 0 {
                let pos = stack.iter().rposition(|&(_, level)| level != 0).unwrap();
                if stack[pos].1 == last  { continue 'L; }
                fail_state.insert(puzzle.hash());
                last = stack[pos].1;
                for (op, _) in stack.drain(pos ..) {
                    undo!(op);
                }
            } else {
                if level == last { continue 'L; }
                fail_state.insert(puzzle.hash());
                last = level; stack.pop(); undo!(op);
            }
            #[cfg(debug_assertions)]
            {
                count += 1;
                eprintln!("[DBG] \x1b[31mRewind #{}\x1b[m", count);
            }
        }
        break;
        //}}}
    }
    #[cfg(debug_assertions)]
    eprintln!("[DBG] \x1b[33m#fail_state = {}\x1b[m", fail_state.len());
    vec![]
}
//}}}

fn main() -> Result<(), &'static str> {
    const N: usize = 4;
    let mut args = std::env::args();
    let prg = args.next().unwrap();
    let Some(s) = args.next() else {
        eprintln!("usage: {} \"comma,separated,string\"", prg);
        return Ok(());
    };
    let board = { //{{{
        let v = s.split(',').collect::<Vec<_>>();
        let mut board = vec![[""; N]; v.len()];
        for (i, s) in v.into_iter().enumerate() {
            let vc = {
                let (mut i, mut vc) = (0, Vec::with_capacity(s.len()));
                for j in s.char_indices().map(|(i, _)| i)
                    .chain(std::iter::once(s.len())).skip(1) {
                    vc.push(unsafe { s.get_unchecked(i .. j) });
                    i = j;
                }
                vc
            };
            if vc.len() > N {
                return Err("Invalid input.");
            }
            board[i][N - vc.len() ..].copy_from_slice(&vc);
        }
        board
    };
    //}}}
    if !wp_check(&board) {
        return Err("Invalid board.");
    }
    let sln = wp_solve(&board);
    if sln.is_empty() {
        println!("No solution.");
        return Ok(());
    }
    let w = sln.len().ilog10() as usize + 1;
    for (i, (a, b)) in sln.into_iter().enumerate() {
        println!("[{:3$}] #{:<4$} \u{2015}\u{2015}\u{2192} #{:<4$}",
            i + 1, a + 1, b + 1,
            w, board.len().ilog10() as usize + 1,
        );
    }
    Ok(())
}
