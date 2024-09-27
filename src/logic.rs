
use rustsat::{
    types::{Lit, Assignment, TernaryVal},
    instances::SatInstance
};

pub trait Generator<T> {
    fn make(instance: &mut SatInstance) -> Self;
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
    fn make(instance: &mut SatInstance) -> Self {
        instance.new_lit()
    }

    fn read_into(self, assignment: &Assignment) -> bool {
        assignment.get_bool(self)
    }
}

impl<const LEN: usize, G, T: Generator<G>> Generator<[G; LEN]> for [T; LEN] {
    fn make(instance: &mut SatInstance) -> Self {
        std::array::from_fn(|_| Generator::make(instance))
    }

    fn read_into(self, assignment: &Assignment) -> [G; LEN] {
        self.map(|x| x.read_into(assignment))
    }
}

