// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

extern crate hamt;
use hamt::HamtRc;
use std::rc::Rc;

#[test]
fn alter_str() {
    // NOTE: Not a great way to use this API because of the all the cloning this data structure does,
    // just testing that this usage is possible.
    let mut hamt = HamtRc::<String, String>::new().insert(&String::from("hello"), &String::from("world"));
    hamt = hamt.alter("hello", |_| Some(String::from("new_world")));
    assert!(hamt["hello"] == "new_world");
}

#[test]
fn alter_rc_str() {
    let hello = Rc::new(String::from("hello"));
    let world = Rc::new(String::from("world"));
    let new_world = Rc::new(String::from("new_world"));
    let mut hamt = HamtRc::<Rc<String>, Rc<String>>::new().insert(&hello, &world);
    hamt = hamt.alter(&hello, |_| Some(new_world.clone()));
    assert!(hamt[&hello] == new_world);
}
