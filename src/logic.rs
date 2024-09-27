use rustsat::{
    types::{Lit, Clause, Assignment, TernaryVal},
    instances::ManageVars,
    clause
};

pub trait Generator<T> {
    fn make<VM: ManageVars>(vm: &mut VM) -> Self;
    fn read_into(self, assignment: &Assignment) -> T;
}

pub trait GetBool {
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

impl Generator<bool> for Lit {
    fn make<VM: ManageVars>(vm: &mut VM) -> Self {
        vm.new_lit()
    }

    fn read_into(self, assignment: &Assignment) -> bool {
        assignment.get_bool(self)
    }
}

impl<const LEN: usize, G, T: Generator<G>> Generator<[G; LEN]> for [T; LEN] {
    fn make<VM: ManageVars>(vm: &mut VM) -> Self {
        std::array::from_fn(|_| Generator::make(vm))
    }

    fn read_into(self, assignment: &Assignment) -> [G; LEN] {
        self.map(|x| x.read_into(assignment))
    }
}

pub trait Logic<T> {
    fn eqs(self, x: T) -> Vec<Clause>;
}

impl Logic<Lit> for Lit {
    fn eqs(self, x: Lit) -> Vec<Clause> {
        vec![clause![!self, x], clause![self, !x]]
    }
}
