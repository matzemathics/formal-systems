use std::clone::Clone;
use std::collections::HashMap;
use std::hash::Hash;
use std::time::Instant;

struct HornClause<Atom> {
  pos: Option<Atom>,
  neg: Vec<Atom>,
}

fn solve_horn<Atom: Eq + Clone>(clauses: &[HornClause<Atom>]) -> Option<Vec<Atom>> {
  let mut res = Vec::new();
  let mut flag = true;

  while flag {
    flag = false;

    for clause in clauses {
      if clause
        .neg
        .iter()
        .map(|n| res.contains(n))
        .find(|&x| x == false)
        .is_none()
      {
        if clause.pos.is_none() {
          return None;
        }

        let new = clause.pos.as_ref().unwrap().clone();

        if !res.contains(&new) {
          flag = true;
          res.push(new);
        }
      }
    }
  }

  Some(res)
}

fn test_horn() {
  let expr = vec![
    HornClause {
      pos: Some(4),
      neg: vec![1, 2, 3],
    },
    HornClause {
      pos: None,
      neg: vec![5, 6],
    },
    HornClause {
      pos: Some(6),
      neg: vec![7, 2],
    },
    HornClause {
      pos: None,
      neg: vec![6, 2],
    },
    HornClause {
      pos: Some(2),
      neg: vec![6, 3],
    },
    HornClause {
      pos: Some(5),
      neg: vec![3, 4],
    },
    HornClause {
      pos: Some(7),
      neg: vec![1],
    },
    HornClause {
      pos: Some(4),
      neg: vec![1, 7],
    },
    HornClause {
      pos: Some(3),
      neg: vec![],
    },
    HornClause {
      pos: Some(1),
      neg: vec![],
    },
  ];

  println!("{:?}", solve_horn(&expr));
}

fn main() {
  println!("Testing kmp flavoured inference");
  let now = Instant::now();
  test_quad(20);
  let elapsed = now.elapsed();
  println!("Time elapsed: {}", elapsed.as_millis());

  let now = Instant::now();
  println!("Testing automaton like inference");
  test_quad_new(20);
  let elapsed = now.elapsed();
  println!("Time elapsed: {}", elapsed.as_millis());
}

struct NtRule<NT> {
  context: Vec<NT>,
  result: Vec<NT>,
  search_pattern: Vec<isize>,
}

impl<NT: Eq + Clone + std::fmt::Debug> NtRule<NT> {
  fn new(context: Vec<NT>, result: Vec<NT>) -> NtRule<NT> {
    let mut search_pattern: Vec<isize> = Vec::new();
    search_pattern.resize(context.len(), -1);

    // how many chars left of i match the beginning
    let mut cmp_index: isize = 0;

    for i in 1..context.len() {
      if context[i] == context[cmp_index as usize] {
        search_pattern[i] = search_pattern[cmp_index as usize]
      } else {
        search_pattern[i] = cmp_index;
      }

      while (cmp_index >= 0) && (context[i] != context[cmp_index as usize]) {
        cmp_index = search_pattern[cmp_index as usize];
      }

      cmp_index += 1;
    }

    NtRule {
      context,
      result,
      search_pattern,
    }
  }

  fn find(&self, input: &Vec<NT>) -> Option<usize> {
    let mut context_pos: isize = 0;

    for input_pos in 0..input.len() {
      while context_pos >= 0 && input[input_pos] != self.context[context_pos as usize] {
        context_pos = self.search_pattern[context_pos as usize]
      }

      context_pos += 1;

      if context_pos == self.context.len() as isize {
        return Some(input_pos + 1 - self.context.len());
      }
    }

    None
  }

  fn apply(&self, input: &mut Vec<NT>) -> bool {
    let offset = self.find(&input);

    if offset.is_none() {
      return false;
    }
    let matched = &mut input[offset.unwrap()..offset.unwrap() + self.context.len()];

    if self.context.len() >= self.result.len() {
      self
        .result
        .iter()
        .zip(matched.iter_mut())
        .for_each(|(val, elem)| *elem = val.clone());
      let rem = self.context.len() - self.result.len();
      if rem > 0 {
        let offset = offset.unwrap() + self.result.len();
        input[offset..].rotate_left(rem);
        input.truncate(input.len() - rem);
      }
    } else {
      let (left, right) = self.result.split_at(matched.len());
      matched
        .iter_mut()
        .zip(left)
        .for_each(|(elem, val)| *elem = val.clone());

      let cutoff = offset.unwrap() + matched.len();
      input.append(&mut right.to_vec());
      input[cutoff..].rotate_right(right.len());
    }

    true
  }
}

#[derive(Eq, PartialEq, Clone, Debug, Hash)]
enum QuadNT {
  B,
  C,
  E,
  F,
  O,
  Oh,
  X,
  Y,
  Y1,
  Yf,
}

#[derive(Debug)]
struct NCFG<NT, Tag> {
  map: HashMap<(NT, Tag), Result<(Vec<NT>, usize), Tag>>,
  next_tag: Tag,
}

trait Tag: Default + Eq + Copy {
  fn next(&self) -> Self;
}

impl Tag for u32 {
  fn next(&self) -> u32 {
    self + 1
  }
}

impl<NT: Eq + Hash + Clone, T: Tag + Hash> NCFG<NT, T> {
  fn new() -> NCFG<NT, T> {
    NCFG {
      map: Default::default(),
      next_tag: Default::default(),
    }
  }

  fn add_rule(&mut self, mut context: Vec<NT>, result: Vec<NT>) -> Option<()> {
    let size = context.len();
    context.reverse();
    if context.is_empty() {
      return None;
    }

    let mut tag: T = Default::default();
    let mut current = context.pop().unwrap();
    while let Some(node) = self.map.get(&(current.clone(), tag)) {
      match node {
        Ok(_) => return None,
        Err(t) => {
          tag = t.clone();
          if context.is_empty() {
            return None;
          }
          current = context.pop().unwrap();
        }
      }
    }

    loop {
      if context.is_empty() {
        self.map.insert((current, tag), Ok((result, size)));
        break;
      }

      self.next_tag = self.next_tag.next();
      self.map.insert((current, tag), Err(self.next_tag));
      tag = self.next_tag;

      if let Some(next) = context.pop() {
        current = next;
      } else {
        break;
      }
    }

    Some(())
  }

  fn find(&self, input: &Vec<NT>) -> Option<(usize, usize, &Vec<NT>)> {
    let mut qs_a: Vec<T> = vec![Default::default()];
    let mut qs_b: Vec<T> = vec![Default::default()];

    for b in input {
      for q in qs_a.drain(..) {
        if let Some(n) = self.map.get(&(b.clone(), q)) {
          match n {
            Ok((res, len)) => {
              let offset = (b as *const _ as usize) - (input.as_ptr() as usize);
              return Some((offset + 1 - len, *len, res))
            },
            Err(tag) => qs_b.push(tag.clone()),
          }
        }
      }
      std::mem::swap(&mut qs_a, &mut qs_b);
      qs_b.push(Default::default());
    }

    None
  }

  fn apply(&self, input: &mut Vec<NT>) -> bool {
    let match_result = self.find(&input);

    if match_result.is_none() {
      return false;
    }

    let (offset, matched_len, replacement) = match_result.unwrap();

    let matched = &mut input[offset..offset + matched_len];

    if matched_len >= replacement.len() {
      replacement
        .iter()
        .zip(matched.iter_mut())
        .for_each(|(val, elem)| *elem = val.clone());
      let rem = matched_len - replacement.len();
      if rem > 0 {
        let offset = offset + replacement.len();
        input[offset..].rotate_left(rem);
        input.truncate(input.len() - rem);
      }
    } else {
      let (left, right) = replacement.split_at(matched.len());
      matched
        .iter_mut()
        .zip(left)
        .for_each(|(elem, val)| *elem = val.clone());

      let cutoff = offset + matched_len;
      input.append(&mut right.to_vec());
      input[cutoff..].rotate_right(right.len());
    }

    true
  }
}

fn test_quad(i: usize) {
  let rules = vec![
    NtRule::new(
      vec![QuadNT::B, QuadNT::C],
      vec![QuadNT::B, QuadNT::X, QuadNT::O, QuadNT::X],
    ),
    NtRule::new(
      vec![QuadNT::O, QuadNT::X, QuadNT::C],
      vec![QuadNT::Y, QuadNT::Oh, QuadNT::X, QuadNT::O],
    ),
    NtRule::new(
      vec![QuadNT::O, QuadNT::X, QuadNT::F],
      vec![QuadNT::E, QuadNT::O],
    ),
    NtRule::new(vec![QuadNT::X, QuadNT::Y], vec![QuadNT::X, QuadNT::Yf]),
    NtRule::new(vec![QuadNT::Yf, QuadNT::Oh], vec![QuadNT::O, QuadNT::Yf]),
    NtRule::new(vec![QuadNT::Yf, QuadNT::X], vec![QuadNT::X, QuadNT::Yf]),
    NtRule::new(vec![QuadNT::Yf, QuadNT::O], vec![QuadNT::O, QuadNT::Yf]),
    NtRule::new(
      vec![QuadNT::Yf, QuadNT::C],
      vec![QuadNT::O, QuadNT::O, QuadNT::X, QuadNT::C],
    ),
    NtRule::new(
      vec![QuadNT::Yf, QuadNT::F],
      vec![QuadNT::O, QuadNT::O, QuadNT::E],
    ),
    NtRule::new(
      vec![QuadNT::O, QuadNT::Y, QuadNT::Oh],
      vec![QuadNT::Oh, QuadNT::Oh, QuadNT::Y1],
    ),
    NtRule::new(vec![QuadNT::Y1, QuadNT::Oh], vec![QuadNT::Oh, QuadNT::Y1]),
    NtRule::new(
      vec![QuadNT::Y1, QuadNT::X],
      vec![QuadNT::Y, QuadNT::X, QuadNT::O],
    ),
    NtRule::new(vec![QuadNT::Oh, QuadNT::Y], vec![QuadNT::Y, QuadNT::Oh]),
    NtRule::new(vec![QuadNT::O, QuadNT::E], vec![QuadNT::E, QuadNT::O]),
    NtRule::new(vec![QuadNT::X, QuadNT::E], vec![QuadNT::E]),
    NtRule::new(vec![QuadNT::B, QuadNT::E, QuadNT::O], vec![QuadNT::O]),
  ];

  let mut input = Vec::new();
  input.resize(i + 2, QuadNT::C);
  input[0] = QuadNT::B;
  input[i + 1] = QuadNT::F;

  'outer: loop {
    for rule in rules.iter() {
      if rule.apply(&mut input) {
        continue 'outer;
      }
    }

    break;
  }
  assert_eq!(input.len(), i * i);
}

fn test_quad_new(i: usize) {
  let rules = vec![
    (
      vec![QuadNT::B, QuadNT::C],
      vec![QuadNT::B, QuadNT::X, QuadNT::O, QuadNT::X],
    ),
    (
      vec![QuadNT::O, QuadNT::X, QuadNT::C],
      vec![QuadNT::Y, QuadNT::Oh, QuadNT::X, QuadNT::O],
    ),
    (
      vec![QuadNT::O, QuadNT::X, QuadNT::F],
      vec![QuadNT::E, QuadNT::O],
    ),
    (vec![QuadNT::X, QuadNT::Y], vec![QuadNT::X, QuadNT::Yf]),
    (vec![QuadNT::Yf, QuadNT::Oh], vec![QuadNT::O, QuadNT::Yf]),
    (vec![QuadNT::Yf, QuadNT::X], vec![QuadNT::X, QuadNT::Yf]),
    (vec![QuadNT::Yf, QuadNT::O], vec![QuadNT::O, QuadNT::Yf]),
    (
      vec![QuadNT::Yf, QuadNT::C],
      vec![QuadNT::O, QuadNT::O, QuadNT::X, QuadNT::C],
    ),
    (
      vec![QuadNT::Yf, QuadNT::F],
      vec![QuadNT::O, QuadNT::O, QuadNT::E],
    ),
    (
      vec![QuadNT::O, QuadNT::Y, QuadNT::Oh],
      vec![QuadNT::Oh, QuadNT::Oh, QuadNT::Y1],
    ),
    (vec![QuadNT::Y1, QuadNT::Oh], vec![QuadNT::Oh, QuadNT::Y1]),
    (
      vec![QuadNT::Y1, QuadNT::X],
      vec![QuadNT::Y, QuadNT::X, QuadNT::O],
    ),
    (vec![QuadNT::Oh, QuadNT::Y], vec![QuadNT::Y, QuadNT::Oh]),
    (vec![QuadNT::O, QuadNT::E], vec![QuadNT::E, QuadNT::O]),
    (vec![QuadNT::X, QuadNT::E], vec![QuadNT::E]),
    (vec![QuadNT::B, QuadNT::E, QuadNT::O], vec![QuadNT::O]),
  ];

  let mut ncfg: NCFG<QuadNT, u32> = NCFG::new();

  for rule in rules {
    ncfg.add_rule(rule.0, rule.1);
  }

  let mut input = Vec::new();
  input.resize(i + 2, QuadNT::C);
  input[0] = QuadNT::B;
  input[i + 1] = QuadNT::F;

  while ncfg.apply(&mut input) { }

  assert_eq!(input.len(), i * i);
}
