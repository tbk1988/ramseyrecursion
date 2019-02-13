extern crate num_bigint as bigint; 
extern crate num_traits;
extern crate num_integer;
use bigint::ToBigInt; 
use bigint::BigInt; 
use num_traits::Pow;

use std::error::Error;
use std::fs::File; 
use std::path::Path; 
use std::io::BufReader;
use std::io::BufRead;
use std::collections::HashMap;
use std::cmp::min;
use std::cmp::max; 
use num_integer::Integer;

/*
 * Converts the numerical &str to an unsigned integer.
 * (Is this a proper Rusty way to do it?)
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
        /* the key is an *ordered* tuple */
        let s = min(ints[0],ints[1]);
        let t = max(ints[0],ints[1]);
        &r.insert((s,t),ints[2]); 
    } 
}

/*
 * Get upper bound for R(x,y), from hash table or something else.
 */
fn rub(x: u64, y: u64, r: &HashMap<(u64,u64),u64>) -> u64 {
    let s = min(x,y);
    let t = max(x,y);
    assert!(s >= 1); // R(<= 0,_) undefined
    match s {
        1 => 1,
        2 => t,
        _ => match r.get(&(s,t)) {
            None => rub(x-1,y,&r) + rub(x,y-1,&r),
            Some(x) => *x,
        },
    }
}

/* Calculate the "shi function" (see documentation for definiton)
 * TODO: Write proper documentation, where the "shi function" is defined.
 */
fn shifn(a: &BigInt, b: &BigInt, c: &BigInt, p: &BigInt, k: &BigInt) -> BigInt {
    let t : BigInt = p-1;
    let tsq = t.pow(2u32);
    let s : BigInt = p-2;
    let ssq = s.pow(2u32);
    let x = 5*p + 8*c - 4;
    let y = (-3)*p + 4*b + 6;
    let z = 48*b.pow(2u32) - 80*b*(&s) + 33*(&ssq);
    let za = (-5)*p + 6*b + 10;
    let zb = 5*p - 4;
    let zc = 172 + 64*c.pow(2u32) - 154*p + 43*p.pow(2u32) + 16*c*zb;
    let ya = 1264 + 48*a.pow(3u32) + 48*b.pow(3u32) + 3*a*z + 24*a.pow(2u32)*za
             - 120*b.pow(2u32)*(&s) + 99*b*(&ssq) - 1328*p + 456*p.pow(2u32) - 54*p.pow(3u32);
    let xa = 1388 + 48*a.pow(2u32) + 48*b.pow(2u32) - 2496*c + 24*a*y - 72*b*&s - 1968*p + 576*c*p + 387*p.pow(2u32);

    8957952*k.pow(4u32) - 248832*k.pow(3u32)*&t*p*x - 6*k*&s*t.pow(3u32)*p.pow(3u32)*xa
      - &s*t.pow(4u32)*p.pow(4u32)*ya + 1728*k.pow(2u32)*tsq*p.pow(2u32)*zc
}

/* Calculate the derivative (wrt k) of the "shi function" */
fn shider(a: &BigInt, b: &BigInt, c: &BigInt, p: &BigInt, k: &BigInt) -> BigInt { 
    let t : BigInt = p-1;
    let s = p-2;
    let x = 5*p + 8*c - 4;
    let y = (-3)*p + 4*b + 6;
    let zb = 5*p - 4;
    let zc = 172 + 64*c.pow(2u32) - 154*p + 43*p.pow(2u32) + 16*c*zb;
    let xa = 1388 + 48*a.pow(2u32) + 48*b.pow(2u32) - 2496*c + 24*a*y - 72*b*&s - 1968*p + 576*c*p + 387*p.pow(2u32);

    35831808*k.pow(3u32) - 746496*k.pow(2u32)*&t*p*x - 6*s*t.pow(3u32)*p.pow(3u32)*xa + 3456*k*t.pow(2u32)*p.pow(2u32)*zc
} 

/*
 * Returns true if the Shi-condition is satisfied for any k such that
 * mi <= k <= ma. Otherwise false.
 */
fn shiopt(a: u64, b: u64, c: u64, p: u64, mi: u64, ma: u64) -> bool { 
    let a = a.to_bigint().unwrap();
    let b = b.to_bigint().unwrap();
    let c = c.to_bigint().unwrap();
    let p = p.to_bigint().unwrap();
    if mi > ma {
        return false;
    } else {
        if 144*mi.to_bigint().unwrap() > (5*&p + 8*&c - 4)*(&p-1) {
            /* In this case the shifunction is convex, and we can
             * use interval halving for its derivative.
             */ 
            let mut cmin = mi.to_bigint().unwrap();
            let mut cminv = shifn(&a,&b,&c,&p,&cmin); 
            let mut cmax = ma.to_bigint().unwrap();
            let mut cmaxv = shifn(&a,&b,&c,&p,&cmax); 
            while &cmax - &cmin > 1.to_bigint().unwrap() {
                if cminv < 0.to_bigint().unwrap() || cmaxv < 0.to_bigint().unwrap() {
                    return true;
                } else {
                   let k = (&cmin+&cmax)/2;
                   let kv = shifn(&a,&b,&c,&p,&k); 
                   let kdv = shider(&a,&b,&c,&p,&k); 
                   if kdv <= 0.to_bigint().unwrap() {
                       cmin = k.clone();
                       cminv = kv.clone(); 
                   } else {
                       cmax = k.clone();
                       cmaxv = kv.clone(); 
                   }
                }
            }
            min(cminv,cmaxv) < 0.to_bigint().unwrap()
        } else {
            /* In this case I've not shown convexity yet, so I have to
             * resort to linear search - this is probably unneccessary.
             */
            for k in mi..ma {
                if shifn(&a,&b,&c,&p,&k.to_bigint().unwrap()) < 0.to_bigint().unwrap() {
                    return true;
                }
            }
            false
        }
    }
}

/*
 * Uses methods from Shi et al. to improve the diagonal entry (d,d) in
 * the Ramsey-table (using current values in r) as much as possible.
 */
fn shi(d: u64, r: &mut HashMap<(u64,u64),u64>) {
    let a = rub(d-1,d,&r)-1;
    let b = rub(d-2,d,&r)-1;
    let c = rub(d-3,d,&r)-1;
    let mut p = rub(d,d,&r)-1;
    println!("> Using Shi et al. to see if R({},{}) \\leq {} is best possible",d,d,p+1);
    loop {
        let mi = (p*(p-1)*(p-5) + 23)/24; // ceil(p/q) = (p+q-1)/q
        let ma = p*(p-1)*b/6;
        if shiopt(a,b,c,p,mi,ma) {
            break;
        } else {
            p = p-1;
        }
    }
    let x = r.entry((d,d)).or_insert(p+1);
    *x = min(*x,p+1);
}

/*
 * Returns by how much we may reduce the currently saved bound, of R(x,y), by
 * applying the folklore recursive bound. If it is not possible to reduce
 * by using this the function returns a negative number.
 */
fn folklore_reduction(x: u64, y: u64, r: &HashMap<(u64,u64),u64>) -> i128 {
    let r1 : u64 = rub(x-1,y,&r);
    let r2 : u64 = rub(x,y-1,&r);
    if r1.is_even() && r2.is_even() {
        (rub(x,y,&r) as i128) - ((r1 + r2 - 1) as i128)
    } else {
        (rub(x,y,&r) as i128) - ((r1 + r2) as i128)
    }
}

/*
 * Returns by how much we may reduce the currently saved bound, of R(x,y), by
 * applying the Huang et al.-bound
 */
fn huang_reduction(x: u64, y: u64, r: &HashMap<(u64,u64),u64>) -> i128 {
    let a: BigInt = (rub(x-2,y,&r)-1).to_bigint().unwrap();
    let b: BigInt = (rub(x,y-2,&r)-1).to_bigint().unwrap(); 
    let mut p = rub(x,y,&r)-1;
    let mut deg_lb = match p.checked_sub(rub(x,y-1,&r)) {
        None => 0,
        Some(x) => x,
    };
    let deg_ub = rub(x-1,y,&r)-1;
    let mut lhs = (p-1)*(p-2-&a); 

    /* TODO: Replace linear search by binary */ 
    loop {
        let mut maxval: BigInt = 0.to_bigint().unwrap();
        let t: BigInt = &a-&b+3*(p-1).to_bigint().unwrap();
        if 6*deg_lb.to_bigint().unwrap() < t && t < 6*deg_ub.to_bigint().unwrap() {
            for k in deg_lb..(deg_ub+1) {
                maxval = max(maxval,&t*k - 3*k.pow(2u32) + (&b-&a)*(p-1));
            }
        } else {
            let vallb = &t*deg_lb - 3*deg_lb.pow(2u32) + (&b-&a)*(p-1);
            let valub = &t*deg_ub - 3*deg_ub.pow(2u32) + (&b-&a)*(p-1);
            maxval = max(vallb,valub)
        }
        if maxval < lhs {
            p = p - 1;
            lhs = (p-1)*(p-2-&a);
            deg_lb = match p.checked_sub(rub(x,y-1,&r)) {
                None => 0,
                Some(x) => x,
            };
        } else {
            break;
        }
    }
    (rub(x,y,&r) as i128) - ((p + 1) as i128)
}

fn main() {
    /* TODO: Change ramsey_file from static to a command line argument
     * (it will change type from &str to String then).
     */
    let ramsey_file = "ramsey_data.txt";

    let mut r = HashMap::new();
    read_ramsey_numbers(&ramsey_file, &mut r);
    let rcopy = r.clone();

    shi(7, &mut r);
    shi(8, &mut r);
    shi(9, &mut r);
    shi(10, &mut r);

    println!("Folklore: R(10,10) \\leq {}", (rub(10,10,&r) as i128)-folklore_reduction(10,10,&r));
    println!("Huang: R(5,7) \\leq {}", (rub(5,7,&r) as i128)-huang_reduction(7,8,&r));

    for (m,n) in r.keys() {
        print!("R({},{}) = {}", m, n, r.get(&(*m,*n)).unwrap());
        if rcopy.contains_key(&(*m,*n)) {
            println!(" = {}", rcopy.get(&(*m,*n)).unwrap());
        } else {
            println!(" (new)");
        }
    }
}
