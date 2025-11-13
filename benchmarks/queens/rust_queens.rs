// Rust solution to the n queens problem

fn safe(col:i32, diag1:i32, diag2:i32, row:i32, qs:&mut Vec<i32>) -> bool {
    for r in row..qs.len() as i32 {
        let c = qs[r as usize];
        if c == col || r - c == diag1 || r + c == diag2 {
            return false;
        }
    }
    return true;
}

fn place_queens(row:i32, col:i32, qs:&mut Vec<i32>) -> bool {
    let n = qs.len() as i32;
    if row < 0 {
        return true;
    } else if col >= n {
        return false;
    } else if safe(col, row - col, row + col, row + 1, qs) {
        qs[row as usize] = col;
        return place_queens(row - 1, 0, qs) ||
               place_queens(row, col + 1, qs);
    } else {
        return place_queens(row, col + 1, qs);
    }
}

fn queens(n:i32) -> Option<Vec<i32>> {
    let mut qs = vec![0; n as usize];
    if place_queens(n - 1, 0, &mut qs) {
        Some(qs)
    } else {
        None
    }
}

fn show_queens(qs:&Vec<i32>) {
    for r in 0..qs.len() as i32{
        for c in 0..qs.len() as i32 {
            if qs[r as usize] == c {
                print!("Q");
            } else {
                print!(".");
            }
        }
        println!("");
    }
}

fn main() {
    let n: i32 = 32;
    match queens(n) {
        Some(qs) => {
            show_queens(&qs);
        },
        None => {
            print!("No solution to {} queens problem.\n", n);
        }
    }   
}
