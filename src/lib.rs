use num_bigint::BigUint;
use num_bigint::BigInt;
use num_bigint::Sign;
use num_bigint::RandBigInt;
use rand::prelude::*;
use std::mem;

/// enum `Point`
/// Point on an Elliptic Curve
/// Can either be a `(x, y)` pair or the point at infinity `Inf`
#[derive(PartialEq, Debug, Clone)]
enum Point {
    Inf,
    Pair { x: BigUint, y: BigUint },
}
/// Elliptic Curve of the form `y^2 = x^3 + ax + b` over GF(p)
/// g is a Point on the curve that is a generator of a cyclic subgroup of E(GF(p))
struct EllipticCurve {
    a: BigUint,
    b: BigUint,
    g: Point,
    p: BigUint,
}

impl EllipticCurve {
    /// Associated function: `new`
    /// returns a new Elliptic Curve object
    ///
    /// Panics:
    /// `new` panics if `a` or `b` are not in GF(p)
    /// `new` panics when a singular elliptic curve is specified, i.e., `4a^3 + 27b^2 = 0`
    /// `new` panics when the point at infinity is given as the point
    /// `new` panics when g is not on the curve specified
    fn new(a: BigUint, b: BigUint, g: Point, p: BigUint) -> EllipticCurve {
        let ref_a = &a;
        let ref_b = &b;
        let ref_g = &g;
        let ref_p = &p;
        if a >= p || b >= p {
            panic!("a or b not in GF(p)");
        }

        if ((BigUint::new(vec!(4)) * ref_a * ref_a * ref_a) +
            (BigUint::new(vec!(27)) * ref_b * ref_b)) % ref_p
            == BigUint::new(vec!(0)) {
            panic!("Singular elliptic curve given");
        }

        match ref_g {
            Point::Inf => panic!("Point at infinity specified as generator"),
            Point::Pair { x, y } => {
                if (y * y) % ref_p != ((x * x * x) + (ref_a * x) + ref_b) % ref_p {
                    panic!("g not on curve");
                }
            },
        };

        EllipticCurve {
            a, b, g, p
        }
    }

    fn point_double(&self, point: &Point) -> Point {
        match point {
            Point::Inf => Point::Inf,
            Point::Pair { x, y } => {
                let delta = (BigUint::new(vec!(3)) * x * x + &self.a) *
                    inverse_mod_p(BigUint::new(vec!(2)) * y, &self.p);
                let mut new_x = &delta * &delta;
                let double_x = BigUint::new(vec!(2)) * x;
                if double_x > new_x {
                    new_x += ((&double_x / &self.p) + BigUint::new(vec!(1))) * &self.p;
                }
                new_x -= double_x;
                new_x %= &self.p;

                let mut new_y = &delta * (&self.p + x - &new_x);
                new_y += &self.p - y;
                new_y %= &self.p;

                Point::Pair { x: new_x, y: new_y }
            }
        }
    }

    fn point_add(&self, p1: &Point, p2: &Point) -> Point {
        if p1 == p2 {
            return self.point_double(p1);
        }
        match p1 {
            Point::Inf => p2.clone(),
            Point::Pair { x: x1, y: y1 } => {
                match p2 {
                    Point::Inf => p1.clone(),
                    Point::Pair { x: x2, y: y2 } => {
                        // check if p1 = -p2
                        if x1 == x2 {
                            return Point::Inf;
                        }
                        let delta = (&self.p + y2 - y1) *
                            inverse_mod_p(&self.p + x2 - x1, &self.p);

                        let mut new_x = (&delta * &delta) + &self.p - x1 + &self.p - x2;
                        new_x %= &self.p;

                        let mut new_y = &self.p + (&delta * (&self.p + x1 - &new_x)) - y1;
                        new_y %= &self.p;

                        Point::Pair { x: new_x, y: new_y }
                    }
                }
            }
        }
    }

    fn point_multiply(&self, x: &BigUint, point: &Point) -> Point {
        let bytes = x.to_bytes_be();
        let mut started = false;
        let mut result_point: Point = point.clone();
        for byte in bytes {
            for i in 0..8 {
                if started {
                    result_point = self.point_double(&result_point);
                    if byte & (1 << (7 - i)) != 0 {
                        result_point = self.point_add(&result_point, point);
                    }
                } else {
                    if byte & (1 << (7 - i)) != 0 {
                        started = true;
                    }
                }
            }
        }
        result_point
    }

    fn dh_public_from_private(&self, private_key: &BigUint) -> Point {
        self.point_multiply(private_key, &self.g)
    }

    fn dh_derive_shared_secret( &self,
                                private_key: &BigUint,
                                other_public_key: &Point) -> Result<BigUint, &'static str> {
        match self.point_multiply(private_key, other_public_key) {
            Point::Inf => Err(""),
            Point::Pair{ x, y: _y } => Ok(x)
        }
    }
}

/// Function `inverse_mod_p`
/// Calculates x^-1 mod p such that x * x^-1 mod p = 1
fn inverse_mod_p(x: BigUint, p: &BigUint) -> BigUint {
    let xmod_p = x % p;
    let signed_zero = BigInt::new(Sign::NoSign, vec![0]);
    let one = BigUint::new(vec!(1));
    let signed_p = BigInt::from_biguint(Sign::Plus, p.clone());
    let mut last: (BigUint, BigInt) = (p.clone(), signed_zero.clone());
    let mut current: (BigUint, BigInt) = (xmod_p, BigInt::new(Sign::Plus, vec![1]));
    let mut next: (BigUint, BigInt);
    while current.0 != one {
        let q = &last.0 / &current.0;
        let r = &last.0 % &current.0;
        next = (r, last.1 - (BigInt::from_biguint(Sign::Plus, q) * &current.1));
        last = mem::replace(&mut current, next);
    }

    let mut result = current.1;
    while result < signed_zero {
        result += &signed_p;
    }
    result %= &signed_p;
    result.to_biguint().unwrap()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_point_equality() {
        let p1 = Point::Inf;
        let p2 = Point::Inf;
        assert_eq!(p1, p2);

        let p1 = Point::Pair { x: BigUint::new(vec![0]), y: BigUint::new(vec![0]) };
        assert!(p1 != p2);
        let p2 = Point::Pair { x: BigUint::new(vec![0]), y: BigUint::new(vec![0]) };
        assert_eq!(p1, p2);

        let p1 = Point::Pair { x: BigUint::new(vec![1]), y: BigUint::new(vec![0]) };
        assert!(p1 != p2);
        assert!(p1 != Point::Inf);
    }

    #[test]
    #[should_panic(expected = "g not on curve")]
    fn test_elliptic_cuve_constructor_bad_g() {
        // produce toy elliptic curve
        let a = BigUint::new(vec!(1));
        let b = BigUint::new(vec!(6));
        let g = Point::Pair {x: BigUint::new(vec!(2)), y: BigUint::new(vec!(3)) };
        let p = BigUint::new(vec!(11));
        let _curve = EllipticCurve::new(a, b, g, p);
    }

    #[test]
    #[should_panic(expected = "Singular elliptic curve given")]
    fn test_elliptic_cuve_constructor_singular() {
        // produce toy singular elliptic curve 4a^3 + 3b^2 = 0
        let a = BigUint::new(vec!(11 - 3));
        let b = BigUint::new(vec!(2));
        let g = Point::Pair {x: BigUint::new(vec!(2)), y: BigUint::new(vec!(3)) };
        let p = BigUint::new(vec!(11));
        let _curve = EllipticCurve::new(a, b, g, p);
    }

    #[test]
    #[should_panic(expected = "a or b not in GF(p)")]
    fn test_elliptic_cuve_constructor_invalid_a() {
        let a = BigUint::new(vec!(12));
        let b = BigUint::new(vec!(2));
        let g = Point::Pair {x: BigUint::new(vec!(2)), y: BigUint::new(vec!(3)) };
        let p = BigUint::new(vec!(11));
        let _curve = EllipticCurve::new(a, b, g, p);
    }

    #[test]
    fn test_inverse_mod_p() {
        let x = BigUint::new(vec!(5));
        let p = BigUint::new(vec!(17));
        assert_eq!(inverse_mod_p(x, &p), BigUint::new(vec!(7)));

        let x = BigUint::new(vec!(5));
        let p = BigUint::new(vec!(11));
        assert_eq!(inverse_mod_p(x, &p), BigUint::new(vec!(9)));
    }

    #[test]
    fn test_point_double() {
        // produce toy elliptic curve
        let a = BigUint::new(vec!(1));
        let b = BigUint::new(vec!(6));
        let g = Point::Pair {x: BigUint::new(vec!(2)), y: BigUint::new(vec!(7)) };
        let p = BigUint::new(vec!(11));
        let curve = EllipticCurve::new(a, b, g, p);
        let point1 = Point::Pair {x: BigUint::new(vec!(2)), y: BigUint::new(vec!(7)) };
        let point2 = Point::Pair {x: BigUint::new(vec!(5)), y: BigUint::new(vec!(2)) };
        assert_eq!(curve.point_double(&point1), point2);
        assert_eq!(curve.point_double(&Point::Inf), Point::Inf);
    }

    #[test]
    fn test_point_add() {
        let a = BigUint::new(vec!(1));
        let b = BigUint::new(vec!(6));
        let g = Point::Pair {x: BigUint::new(vec!(2)), y: BigUint::new(vec!(7)) };
        let p = BigUint::new(vec!(11));
        let curve = EllipticCurve::new(a, b, g, p);
        let point1 = Point::Pair {x: BigUint::new(vec!(5)), y: BigUint::new(vec!(2)) };
        let point2 = Point::Pair {x: BigUint::new(vec!(2)), y: BigUint::new(vec!(7)) };
        let point3 = Point::Pair {x: BigUint::new(vec!(8)), y: BigUint::new(vec!(3)) };
        assert_eq!(curve.point_add(&point1, &point2), point3);
        assert_eq!(curve.point_add(&point2, &point2), point1);
    }

    #[test]
    fn test_point_multiply() {
        let a = BigUint::new(vec!(1));
        let b = BigUint::new(vec!(6));
        let g = Point::Pair {x: BigUint::new(vec!(2)), y: BigUint::new(vec!(7)) };
        let p = BigUint::new(vec!(11));
        let curve = EllipticCurve::new(a, b, g, p);
        let x = BigUint::new(vec!(2));
        let point1 = Point::Pair {x: BigUint::new(vec!(2)), y: BigUint::new(vec!(7)) };
        let point2 = Point::Pair {x: BigUint::new(vec!(5)), y: BigUint::new(vec!(2)) };
        assert_eq!(curve.point_multiply(&x, &point1), point2);
        let y = BigUint::new(vec!(9));
        let point3 = Point::Pair {x: BigUint::new(vec!(10)), y: BigUint::new(vec!(9)) };
        assert_eq!(curve.point_multiply(&y, &point1), point3);
    }

    #[test]
    fn test_real_curve() {
        let secp256k1: EllipticCurve = EllipticCurve::new(
            BigUint::new(vec!(0)),
            BigUint::new(vec!(7)),
            Point::Pair {
                x: BigUint::parse_bytes(
                    b"79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798",
                    16).unwrap(),
                y: BigUint::parse_bytes(
                    b"483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8",
                    16).unwrap() },
            BigUint::parse_bytes(
                b"FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F", 16).unwrap());
        let k = BigUint::new(vec!(20));
        let x = BigUint::parse_bytes(
            b"4CE119C96E2FA357200B559B2F7DD5A5F02D5290AFF74B03F3E471B273211C97", 16).unwrap();
        let y = BigUint::parse_bytes(
            b"12BA26DCB10EC1625DA61FA10A844C676162948271D96967450288EE9233DC3A", 16).unwrap();
        let res = secp256k1.dh_public_from_private(&k);
        assert_eq!(res, Point::Pair { x, y });

        let k2 = BigUint::parse_bytes(
            b"112233445566778899112233445566778899", 10).unwrap();
        let x2 = BigUint::parse_bytes(
            b"E5A2636BCFD412EBF36EC45B19BFB68A1BC5F8632E678132B885F7DF99C5E9B3", 16).unwrap();
        let y2 = BigUint::parse_bytes(
            b"736C1CE161AE27B405CAFD2A7520370153C2C861AC51D6C1D5985D9606B45F39", 16).unwrap();
        let res2 = secp256k1.dh_public_from_private(&k2);
        assert_eq!(res2, Point::Pair{ x: x2, y: y2 });

        // test size of cyclic group, must return point at infinity
        let n = BigUint::parse_bytes(
            b"FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141", 16).unwrap();

        let res3 = secp256k1.dh_public_from_private(&n);
        assert_eq!(res3, Point::Inf);
    }

    #[test]
    fn test_dh() {
        let secp256k1: EllipticCurve = EllipticCurve::new(
            BigUint::new(vec!(0)),
            BigUint::new(vec!(7)),
            Point::Pair {
                x: BigUint::parse_bytes(
                    b"79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798",
                    16).unwrap(),
                y: BigUint::parse_bytes(
                    b"483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8",
                    16).unwrap() },
            BigUint::parse_bytes(
                b"FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F", 16).unwrap());

        let n = BigUint::parse_bytes(
            b"FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141", 16).unwrap();
        let mut rng: ThreadRng = rand::thread_rng();
        for _i in 0..10 {
            let a = RandBigInt::gen_biguint_below(&mut rng, &n);
            let pub_a = secp256k1.dh_public_from_private(&a);

            let b = RandBigInt::gen_biguint_below(&mut rng, &n);
            let pub_b = secp256k1.dh_public_from_private(&b);

            let k_a = secp256k1.dh_derive_shared_secret(&a, &pub_b).unwrap();
            let k_b = secp256k1.dh_derive_shared_secret(&b, &pub_a).unwrap();

            assert_eq!(k_a, k_b);
        }
    }
}
