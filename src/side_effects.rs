pub(crate) trait SideEffects: SideEffectsClone {
    fn println(&mut self, text: &str);
    fn eprintln(&mut self, text: &str);
}

pub(crate) trait SideEffectsClone {
    fn clone_box(&self) -> Box<dyn SideEffects>;
}

impl<T> SideEffectsClone for T
where
    T: 'static + SideEffects + Clone,
{
    fn clone_box(&self) -> Box<dyn SideEffects> {
        Box::new(self.clone())
    }
}

impl Clone for Box<dyn SideEffects> {
    fn clone(&self) -> Self {
        self.clone_box()
    }
}

#[derive(Default, Copy, Clone)]
pub struct StandardSideEffects;

impl SideEffects for StandardSideEffects {
    fn println(&mut self, text: &str) {
        println!("{}", text);
    }

    fn eprintln(&mut self, text: &str) {
        eprintln!("{}", text);
    }
}
