#[derive(Clone)]
enum List {
    Nil,
    Cons(i32, Box<List>),
}

impl List {
    // Generate a list from a range [start, end)
    fn from_to(start: i32, end: i32) -> List {
        if start >= end {
            List::Nil
        } else {
            List::Cons(start, Box::new(List::from_to(start + 1, end)))
        }
    }

    // Compute the length of the list
    fn len(&self) -> usize {
        match self {
            List::Nil => 0,
            List::Cons(_, tail) => 1 + tail.len(),
        }
    }

    // Non-destructive append: returns a new list
    fn append(&self, other: &List) -> List {
        match self {
            List::Nil => other.clone(),
            List::Cons(head, tail) => List::Cons(*head, Box::new(tail.append(other))),
        }
    }

    // Naive recursive reverse: O(n^2), non-destructive
    fn reverse(&self) -> List {
        match self {
            List::Nil => List::Nil,
            List::Cons(head, tail) => tail.reverse().append(&List::Cons(*head, Box::new(List::Nil))),
        }
    }
}

fn main() {
    let list = List::from_to(0, 100_000);
    let reversed = list.reverse();
    println!("Reversed list size = {}", reversed.len());
}

// Testing code
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
//  }

