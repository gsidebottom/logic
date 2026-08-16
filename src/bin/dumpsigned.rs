//! Dump exact signed coefficients (621) of a 3x3x23 bits file, one
//! space-separated line per sign model, for downstream .sms emission.
use logic::zrescore::*;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let path = &args[0];
    let n: usize = args.get(1).map(|s| s.parse().unwrap()).unwrap_or(1);
    let bits: Vec<u8> = std::fs::read_to_string(path)
        .unwrap()
        .chars()
        .filter(|c| c.is_ascii_digit())
        .map(|c| (c as u8) - b'0')
        .collect();
    assert_eq!(bits.len(), NV);
    let eqs = brent_equations();
    for coef in sign_models(&bits, n, &eqs) {
        println!("{}", coef.iter().map(|c| c.to_string())
                 .collect::<Vec<_>>().join(" "));
    }
}
