extern crate quickcheck;
extern crate hamt;
use quickcheck::{Arbitrary, Gen, quickcheck};
use std::collections::HashMap;
use hamt::HamtRc;

#[derive(Copy, Clone, Debug)]
enum Command {
    Insert(isize, isize),
    Remove(isize),
    CheckEquals(isize),
}

impl Arbitrary for Command {
    fn arbitrary<G: Gen>(g: &mut G) -> Self {
        let cmd: usize = Arbitrary::arbitrary(g);
        let key: isize = Arbitrary::arbitrary(g);
        match cmd % 5 {
            0 => {
                Command::CheckEquals(key % 200)
            }
            1 => {
                Command::Remove(key % 200)
            }
            _ => {
                let value: isize = Arbitrary::arbitrary(g);
                Command::Insert(key % 200, value % 200)
            }
        }
    }
}

#[derive(Clone, Debug)]
struct Commands {
    cmds: Vec<Command>,
}

impl Arbitrary for Commands {
    fn arbitrary<G: Gen>(g: &mut G) -> Self {
        let mut cmds = Vec::new();
        for _ in 0..50000 {
            cmds.push(Arbitrary::arbitrary(g));
        }
        return Commands { cmds: cmds };
    }
}

fn simulation_testing(v: Commands) -> bool {
    let mut hamt: HamtRc<isize, isize> = HamtRc::new();
    let mut hashmap: HashMap<isize, isize> = HashMap::new();
    for cmd in v.cmds {
        match cmd {
            Command::Insert(k, v) => {
                hamt = hamt.insert(&k, &v);
                hashmap.insert(k, v);

                if hamt.contains_key(&k) != hashmap.contains_key(&k) {
                    return false;
                }
            }
            Command::Remove(k) => {
                hamt = hamt.remove(&k);
                hashmap.remove(&k);

                if hamt.contains_key(&k) != hashmap.contains_key(&k) {
                    return false;
                }
            }
            Command::CheckEquals(k) => {
                if hamt.get(&k) != hashmap.get(&k) {
                    return false;
                }
            }
        }
        if hamt.len() != hashmap.len() {
            return false;
        }
    }

    for (key, val) in &hashmap {
        if &hamt[key] != val {
            return false;
        }
    }

    for (key, val) in &hamt {
        if &hashmap[key] != val {
            return false;
        }
    }
    return true;
}

#[test]
fn test_simulation_testing() {
    quickcheck(simulation_testing as fn(Commands) -> bool);
}
