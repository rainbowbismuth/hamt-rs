// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

extern crate quickcheck;
extern crate hamt;
extern crate rand;
use quickcheck::{Arbitrary, Gen, quickcheck};
use std::collections::HashSet;
use rand::Rng;
use hamt::HamtRc;

#[derive(Copy, Clone, Debug)]
struct Command {
    key: isize,
    val: isize,
}

#[derive(Clone, Debug)]
struct Commands {
    cmds: Vec<Command>,
}

impl Arbitrary for Commands {
    fn arbitrary<G: Gen>(g: &mut G) -> Self {
        let mut cmds = Vec::new();
        let mut seen = HashSet::new();
        for _ in 0..500000 {
            let key: isize = Arbitrary::arbitrary(g);
            let val: isize = Arbitrary::arbitrary(g);
            if !seen.contains(&key) {
                seen.insert(key);
                cmds.push(Command {
                    key: key,
                    val: val,
                });
            }
        }
        Commands { cmds: cmds }
    }
}

fn equality_test(v: Commands) -> bool {
    let mut rng = rand::thread_rng();
    let mut shuffled = v.cmds.clone();
    rng.shuffle(&mut shuffled);

    let mut m1 = HamtRc::new();
    for cmd in &v.cmds {
        m1 = m1.insert(&cmd.key, &cmd.val);
    }
    let mut m2 = HamtRc::new();
    for cmd in shuffled {
        m2 = m2.insert(&cmd.key, &cmd.val);
    }
    m1 == m2
}

#[test]
fn test_prop_equality_test() {
    quickcheck(equality_test as fn(Commands) -> bool);
}
