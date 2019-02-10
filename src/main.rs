use std::error::Error;
use std::fs::File; 
use std::path::Path; 
use std::io::BufReader;
use std::io::BufRead;
use std::collections::HashMap;

/*
 * Converts the numerical &str to an unsigned integer.
 * (Is this a good Rust way to do it?)
 */
fn str_to_u32(s: &str) -> u64{
    match s.to_string().parse() {
        Err(_) => panic!("{} is not an unsigned integer!", s.to_string()),
        Ok(p) => p,
    }
}

/*
 * Opens file in [filename] and reads lines formatted like:
 *   "NUM1 NUM2 NUM3"
 * where NUMi is a numerical string. It sets the hashmap r conatining
 * Ramsey numbers so that R(NUM1,NUM2) = NUM3.
 */
fn read_ramsey_numbers(filename: &str, r: &mut HashMap<(u64,u64),u64>) {
    let path = Path::new(filename);
    let display = path.display();

    let f = match File::open(&path) {
        Err(why) => panic!("Could not open {}: {}", display, why.description()),
        Ok(file) => file,
    }; 

    let file = BufReader::new(&f);

    for line in file.lines() {
        let unwrapped = match line {
            Err(why) => panic!("Could not read line!: {}", why.description()),
            Ok(u) => u,
        };
        let splat = unwrapped.split_whitespace();
        let ints: Vec<u64> = splat.map(str_to_u32).collect();
        &r.insert((ints[0],ints[1]),ints[2]); 
    } 
}

/*
 * Uses methods from Shi et al. to improve the diagonal entry (d,d) in
 * the Ramsey-table (using current values in r) as much as possible.
 */
fn shi(d: u64, r: &mut HashMap<(u64,u64),u64>) {
    r.insert((d,d),0);
}

fn main() {
    /* TODO: Change ramsey_file from static to a command line argument
     * (it will change type from &str to String then).
     */
    let ramsey_file = "ramsey_data.txt";

    let mut r = HashMap::new();
    read_ramsey_numbers(&ramsey_file, &mut r);
    let rcopy = r.clone();

    shi(4, &mut r);

    for (m,n) in r.keys() {
        print!("R({},{}) = {}", m, n, r.get(&(*m,*n)).unwrap());
        if rcopy.contains_key(&(*m,*n)) {
            println!(" = {}", rcopy.get(&(*m,*n)).unwrap());
        } else {
            println!(" (new)");
        }
    } 
}
