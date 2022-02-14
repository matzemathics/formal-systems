use std::clone::Clone;

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
  test_quad(1);
  println!("===================================");
  test_quad(2);
  println!("===================================");
  test_quad(3);
}

struct NtRule<NT> {
  context: Vec<NT>,
  result: Vec<NT>,
  search_pattern: Vec<isize>
}

impl<NT: Eq + Clone + std::fmt::Debug> NtRule<NT> {

  fn new(context: Vec<NT>, result: Vec<NT>) -> NtRule<NT> {
    let mut search_pattern : Vec<isize> = Vec::new();
    search_pattern.resize(context.len(), -1);

    // how many chars left of i match the beginning
    let mut cmp_index: isize = 0;

    for i in 1..context.len() {
      if context[i] == context[cmp_index as usize] {
        search_pattern[i] = search_pattern[cmp_index as usize]
      }
      else {
        search_pattern[i] = cmp_index;
      }

      while (cmp_index >= 0) && (context[i] != context[cmp_index as usize]) {
        cmp_index = search_pattern[cmp_index as usize];
      }

      cmp_index += 1;
    }

    NtRule { context, result, search_pattern }
  }

  fn find(&self, input: &Vec<NT>) -> Option<usize> {
    let mut context_pos: isize = 0;

    for input_pos in 0..input.len() {
      while context_pos >= 0 && input[input_pos] != self.context[context_pos as usize] {
        context_pos = self.search_pattern[context_pos as usize]
      }

      context_pos += 1;

      if context_pos == self.context.len() as isize {
        return Some(input_pos + 1 - self.context.len())
      }
    }

    None
  }

  fn apply(&self, mut input: Vec<NT>) -> Result<Vec<NT>, Vec<NT>> {
    let offset = self.find(&input);

    if offset.is_none() { return Err(input); }
    let matched = &mut input[offset.unwrap() .. offset.unwrap() + self.context.len()];

    if self.context.len() >= self.result.len() {
      self.result.iter().zip(matched.iter_mut()).for_each(|(val, elem)| *elem = val.clone());
      let rem = self.context.len() - self.result.len();
      
      if rem > 0 {
        let offset = offset.unwrap() + self.result.len();
        input[offset..].rotate_left(rem);
        input.truncate(input.len() - rem);
      }
    }
    else {
      let (left, right) = self.result.split_at(matched.len());
      matched.iter_mut().zip(left).for_each(|(elem, val)| *elem = val.clone());

      let cutoff = offset.unwrap() + matched.len();
      input.append(&mut right.to_vec());
      input[cutoff..].rotate_right(right.len());
    }

    Ok(input)
  }

}

#[derive(Eq, PartialEq, Clone, Debug)]
enum QuadNT { B, C, E, F, O, Oh, X, Y, Y1, Yf }

fn test_quad(i: usize) {

  let rules = vec![
    NtRule::new(vec![QuadNT::B, QuadNT::C], vec![QuadNT::B, QuadNT::X, QuadNT::O, QuadNT::X]),
    NtRule::new(vec![QuadNT::O, QuadNT::X, QuadNT::C], vec![QuadNT::Y, QuadNT::Oh, QuadNT::X, QuadNT::O]),
    NtRule::new(vec![QuadNT::O, QuadNT::X, QuadNT::F], vec![QuadNT::E, QuadNT::O]),
    NtRule::new(vec![QuadNT::X, QuadNT::Y], vec![QuadNT::X, QuadNT::Yf]),
    NtRule::new(vec![QuadNT::Yf, QuadNT::Oh], vec![QuadNT::O, QuadNT::Yf]),
    NtRule::new(vec![QuadNT::Yf, QuadNT::X], vec![QuadNT::X, QuadNT::Yf]),
    NtRule::new(vec![QuadNT::Yf, QuadNT::O], vec![QuadNT::O, QuadNT::Yf]),
    NtRule::new(vec![QuadNT::Yf, QuadNT::C], vec![QuadNT::O, QuadNT::O, QuadNT::X, QuadNT::C]),
    NtRule::new(vec![QuadNT::Yf, QuadNT::F], vec![QuadNT::O, QuadNT::O, QuadNT::E]),
    NtRule::new(vec![QuadNT::O, QuadNT::Y, QuadNT::Oh], vec![QuadNT::Oh, QuadNT::Oh, QuadNT::Y1]),
    NtRule::new(vec![QuadNT::Y1, QuadNT::Oh], vec![QuadNT::Oh, QuadNT::Y1]),
    NtRule::new(vec![QuadNT::Y1, QuadNT::X], vec![QuadNT::Y, QuadNT::X, QuadNT::O]),
    NtRule::new(vec![QuadNT::Oh, QuadNT::Y], vec![QuadNT::Y, QuadNT::Oh]),
    NtRule::new(vec![QuadNT::O, QuadNT::E], vec![QuadNT::E, QuadNT::O]),
    NtRule::new(vec![QuadNT::X, QuadNT::E], vec![QuadNT::E]),
    NtRule::new(vec![QuadNT::B, QuadNT::E, QuadNT::O], vec![QuadNT::O])
  ];

  let mut flag = true;

  let mut input = Vec::new();
  input.resize(i + 2, QuadNT::C);
  input[0] = QuadNT::B;
  input[i+1] = QuadNT::F;

  while flag {
    println!("{:?}", input);
    flag = false;

    for rule in rules.iter() {
      match rule.apply(input) {
        Ok(new) => { 
          input = new;
          flag = true;
          break;
        }
        Err(old) => {
          input = old;
        }
      }
    }
  }
}