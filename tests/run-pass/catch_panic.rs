use std::panic::catch_unwind;

fn do_panic() {
    panic!("Hello from panic!");
}

fn main() {
    let res = catch_unwind(do_panic);
    let expected: Box<&str> = Box::new("Hello from panic!");
    let actual = res.expect_err("do_panic() did not panic!")
        .downcast::<&'static str>().expect("Failed to cast to string!");
        
    assert_eq!(expected, actual);
}

