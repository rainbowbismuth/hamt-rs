extern crate hamt;
use hamt::HamtRc;

#[test]
fn alter_str() {
    // NOTE: Not a great way to use this API because of the all the cloning this data structure does,
    // just testing that this usage is possible.
    let mut hamt = HamtRc::<String, String>::new().insert(String::from("hello"), String::from("world"));
    hamt = hamt.alter("hello", |_| Some(String::from("new_world")));
    assert!(hamt["hello"] == "new_world");
}
