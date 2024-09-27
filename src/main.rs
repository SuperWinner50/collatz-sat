use rustsat::{
    types::{Lit, Clause, Assignment},
    instances::{SatInstance, ManageVars},
    solvers::Solve,
    encodings::CollectClauses,
    clause
};

use rustsat_glucose::core::Glucose;

mod logic;
use logic::*;

struct Math<'a, const LEN: usize, VM> {
    vm: &'a mut VM,
    clauses: Vec<Clause>,
    x: Bin<LEN>,
}

impl<'a, const LEN: usize, VM: ManageVars> Math<'a, LEN, VM> {
    fn new(vm: &'a mut VM, x: Bin<LEN>) -> Self {
        Math {
            vm,
            clauses: Vec::new(),
            x
        }
    }

    fn rshift(mut self, output: Option<Bin<LEN>>) -> Self {
        let out = output.unwrap_or_else(|| Bin::<LEN>::make(self.vm));

        for i in 1..LEN {
            self.clauses.extend(self.x.num[i].eqs(out.num[i-1]));
        }

        self.clauses.push(clause![!out.num[LEN - 1]]);

        self.x = out;
        self
    }

    fn lshift(mut self, output: Option<Bin<LEN>>) -> Self { 
        let out = output.unwrap_or_else(|| Bin::<LEN>::make(self.vm));

        for i in 1..LEN {
            self.clauses.extend(out.num[i].eqs(self.x.num[i-1]));
        }

        self.clauses.push(clause![!out.num[0]]);

        self.x = out;
        self
    }

    fn plus(mut self, y: Bin<LEN>, output: Option<Bin<LEN>>) -> Self {
        let out = output.unwrap_or_else(|| Bin::<LEN>::make(self.vm));

        self.clauses.extend(xor(self.x.num[0], y.num[0], out.num[0]));
        
        let mut carry = self.vm.new_lit();
        self.clauses.extend(and(self.x.num[0], y.num[0], carry));

        for i in 1..LEN {
            self.clauses.extend(
                xor3(self.x.num[i], y.num[i], carry, out.num[i]));
            
            if i == LEN - 1 {
                break;
            }

            let c2 = self.vm.new_lit();
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
    fn make<VM: ManageVars>(vm: &mut VM) -> Self {
        Bin {
            num: std::array::from_fn(|_| vm.new_lit()),
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

// y = a and b or b and c or a and c
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

const STEPS: usize = 20;

fn main() {
    let mut instance = SatInstance::new();

    let mut n = Bin::<32>::make(instance.var_manager_mut());
    n.as_eq(12345, &mut instance);
    
    let one = Bin::make(instance.var_manager_mut());
    one.as_eq(1, &mut instance);

    for _ in 0..STEPS {
        let n2 = Bin::make(instance.var_manager_mut());

        let (clauses_odd, _) = Math::new(instance.var_manager_mut(), n)
            .lshift(None)
            .plus(n, None)
            .plus(one, Some(n2))
            .out();

        let (clauses_even, _) = Math::new(instance.var_manager_mut(), n)
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

    let n = n.read_into(&assignment);
    println!("{}", n);
}
