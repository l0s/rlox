pub trait SideEffects {
    fn println(&mut self, text: &str);
    // fn eprintln(&mut self, text: &str);
}

#[derive(Default)]
pub struct StandardSideEffects;

impl SideEffects for StandardSideEffects {
    fn println(&mut self, text: &str) {
        println!("{}", text);
    }

    // fn eprintln(&mut self, text: &str) {
    //     eprintln!("{}", text);
    // }
}
