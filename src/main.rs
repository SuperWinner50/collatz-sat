use rustsat::{
    types::{Lit, Clause, Assignment, TernaryVal},
    instances::SatInstance,
    solvers::Solve,
    encodings::CollectClauses,
    clause
};

use rustsat_glucose::core::Glucose;

mod logic;
use logic::*;

trait Logic<T> {
    fn eqs(self, x: T) -> Vec<Clause>;
}

trait GetBool {
    fn get_bool(&self, lit: Lit) -> bool;
}

impl GetBool for Assignment {
    fn get_bool(&self, lit: Lit) -> bool {
        match self.lit_value(lit) {
            TernaryVal::True => true,
            TernaryVal::False => false,
            TernaryVal::DontCare => panic!("Bad lit")
        }
    }
}

struct Math<'a, const LEN: usize> {
    instance: &'a mut SatInstance,
    clauses: Vec<Clause>,
    x: Bin<LEN>,
}

impl<'a, const LEN: usize> Math<'a, LEN> {
    fn new(instance: &'a mut SatInstance, x: Bin<LEN>) -> Self {
        Math {
            instance,
            clauses: Vec::new(),
            x
        }
    }

    fn rshift(mut self, output: Option<Bin<LEN>>) -> Self {
        let out = output.unwrap_or_else(|| Bin::<LEN>::make(self.instance));

        for i in 1..LEN {
            self.clauses.extend(self.x.num[i].eqs(out.num[i-1]));
        }

        self.clauses.push(clause![!out.num[LEN - 1]]);

        self.x = out;
        self
    }

    fn lshift(mut self, output: Option<Bin<LEN>>) -> Self { 
        let out = output.unwrap_or_else(|| Bin::<LEN>::make(self.instance));

        for i in 1..LEN {
            self.clauses.extend(out.num[i].eqs(self.x.num[i-1]));
        }

        self.clauses.push(clause![!out.num[0]]);

        self.x = out;
        self
    }

    fn plus(mut self, y: Bin<LEN>, output: Option<Bin<LEN>>) -> Self {
        let out = output.unwrap_or_else(|| Bin::<LEN>::make(self.instance));

        self.clauses.extend(xor(self.x.num[0], y.num[0], out.num[0]));
        
        let mut carry = self.instance.new_lit();
        self.clauses.extend(and(self.x.num[0], y.num[0], carry));

        for i in 1..LEN {
            self.clauses.extend(
                xor3(self.x.num[i], y.num[i], carry, out.num[i]));
            
            if i == LEN - 1 {
                break;
            }

            let c2 = self.instance.new_lit();
            self.clauses.extend(carry_out(self.x.num[i], y.num[i], carry, c2));

            carry = c2;
        }
        
        self.x = out;
        self
    }

    fn out(self) -> (Vec<Clause>, Bin<LEN>) {
        (self.clauses, self.x)
    }
}

#[derive(Clone, Copy)]
struct Bin<const LEN: usize> {
    num: [Lit; LEN]
}

impl<const LEN: usize> Bin<LEN> {
    fn as_eq(&self, mut x: u32, instance: &mut SatInstance) {
        for v in self.num {
            instance.add_unit(if x & 1 == 1 { v } else { !v });
            x >>= 1;
        }
    }
}

impl<const LEN: usize> Generator<u64> for Bin<LEN> {
    fn make(instance: &mut SatInstance) -> Self {
        Bin {
            num: std::array::from_fn(|_| instance.new_lit()),
        }
    }

    fn read_into(self, assignment: &Assignment) -> u64 {
        (0..LEN)
            .map(|i| (1 << i) * (assignment.get_bool(self.num[i]) as u64))
            .sum::<u64>()
    }
}

// y = a xor b
fn xor(a: Lit, b: Lit, y: Lit) -> Vec<Clause> {
    vec![
        clause![!a, !b, !y],
        clause![!a, b, y],
        clause![a, !b, y],
        clause![a, b, !y]
    ]
}

// y = (a xor b) xor c 
fn xor3(a: Lit, b: Lit, c: Lit, y: Lit) -> Vec<Clause> {
    vec![
        clause![!a, !b, !c, y], clause![!a, !b, c, !y],
        clause![!a, b, !c, !y], clause![!a, b, c, y],
        clause![a, !b, !c, !y], clause![a, !b, c, y],
        clause![a, b, !c, y], clause![a, b, c, !y]
    ]
}

// y = a and b
fn and(a: Lit, b: Lit, y: Lit) -> Vec<Clause> {
    vec![
        clause![!a, !b, y],
        clause![a, !y],
        clause![b, !y]
    ]
}

fn carry_out(a: Lit, b: Lit, c: Lit, y: Lit) -> Vec<Clause> {
    vec![
        clause![!a, !b, y],
        clause![!a, !c, y],
        clause![!b, !c, y],
        clause![a, b, !y],
        clause![a, c, !y],
        clause![b, c, !y]
    ]
}

impl Logic<Lit> for Lit {
    fn eqs(self, x: Lit) -> Vec<Clause> {
        vec![clause![!self, x], clause![self, !x]]
    }   
}

const STEPS: usize = 984;

fn main() {
    let mut instance = SatInstance::new();

    let mut n = Bin::<128>::make(&mut instance);
    n.as_eq(670617279, &mut instance);

    let one = Bin::make(&mut instance);
    one.as_eq(1, &mut instance);

    for _ in 0..STEPS {
        let n2 = Bin::make(&mut instance);

        let (clauses_odd, _) = Math::new(&mut instance, n)
            .lshift(None)
            .plus(n, None)
            .plus(one, Some(n2))
            .out();

        let (clauses_even, _) = Math::new(&mut instance, n)
            .rshift(Some(n2))
            .out();

        instance.extend_clauses(
            clauses_odd.into_iter().map(|mut c| { c.add(!n.num[0]); c })
        ).unwrap();

        instance.extend_clauses(
            clauses_even.into_iter().map(|mut c| { c.add(n.num[0]); c })
        ).unwrap();
 
        n = n2;
    }

    let (cnf, _) = instance.into_cnf();

    let mut glucose = Glucose::default();
    glucose.add_cnf(cnf).unwrap();

    glucose.solve().unwrap();
    let assignment = glucose.full_solution().expect("No solution");
    // println!("{:?}", assignment);

    let n = n.read_into(&assignment);
    println!("{}", n);
}
