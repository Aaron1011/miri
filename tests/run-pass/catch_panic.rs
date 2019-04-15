use std::panic::catch_unwind;
use std::cell::Cell;

thread_local! {
    static MY_COUNTER: Cell<usize> = Cell::new(0);
}

fn aaron_do_panic() {
    let old_val = MY_COUNTER.with(|c| {
        let val = c.get();
        c.set(val + 1);
        val
    });
    panic!(format!("Hello from panic: {:?}", old_val));
}

fn main() {
    println!("Main called!");
    std::panic::set_hook(Box::new(|info| {
        println!("Custom panic hook: location: {:?} payload: {:?}", info.location(), info.payload().downcast_ref::<String>());
    }));
    let res = catch_unwind(aaron_do_panic);
    let expected: Box<String> = Box::new("Hello from panic: 0".to_string());
    let actual = res.expect_err("do_panic() did not panic!")
        .downcast::<String>().expect("Failed to cast to string!");
        
    assert_eq!(expected, actual);
    //println!("Actual: {:?}", actual);
}

