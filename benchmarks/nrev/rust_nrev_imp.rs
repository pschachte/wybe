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
    fn append(self, other: List) -> List {
        match self {
            List::Nil => other,
            List::Cons(head, mut tail) => {
                // mutate the tail pointer, rather than making a new one
                *tail = tail.append(other);
                List::Cons(head, tail)
            }
        }
    }

    fn reverse(self) -> List {
        match self {
            List::Nil => List::Nil,
            List::Cons(head, tail) =>
                tail.reverse()
                    .append(List::Cons(head, Box::new(List::Nil))),
        }
    }
}

fn main() {
    let list = List::from_to(0, 100_000);
    let reversed = list.reverse();
    println!("{}", reversed.len());
}
