#[derive(Clone)]
enum List {
    Nil,
    Cons(i32, Box<List>),
}

impl List {
    // Generate a list from a range [start, end)
    fn from_to(start: i32, end: i32) -> List {
        let mut result = List::Nil;
        for value in (start..end).rev() {
            result = List::Cons(value, Box::new(result));
        }
        result
    }

    // Compute the length of the list
    fn len(&self) -> usize {
        let mut count = 0;
        let mut current = self;
        while let List::Cons(_, next) = current {
            count += 1;
            current = next;
        }
        count
    }

    // Destructive append
    fn append(mut self : &mut List, other: List) {
        while let List::Cons(_, next) = self {
            self = next;
        }
        *self = other;
    }

    fn reverse(self) -> List {
        match self {
            List::Nil => List::Nil,
            List::Cons(head, box_tail) => {
                let mut rtail = box_tail.reverse();
                rtail.append(List::Cons(head, Box::new(List::Nil)));
                rtail
            }
        }
    }
}

fn main() {
    let list = List::from_to(0, 100_000);
    let reversed = list.reverse();
    println!("Reversed list size = {}", reversed.len());
}

// // Testing code
// impl List {
//     // Print the list (for debugging)
//     #[allow(dead_code)]
//     fn print_list(&self) {
//         match self {
//             List::Nil => println!("[]"),
//             List::Cons(head, tail) => {
//                 print!("[{}", head);
//                 let mut current = tail;
//                 while let List::Cons(h, t) = &**current {
//                     print!(", {}", h);
//                     current = t;
//                 }
//                 println!("]");
//             }
//         }
//     }
// }

// fn main() {
//     let list = List::from_to(0, 10);
//     list.print_list();
//     let reversed = list.reverse();
//     reversed.print_list();
//     println!("length = {}", reversed.len());
// }
