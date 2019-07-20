
use num_bigint::BigUint;

/// enum `Point`
/// Point on an Elliptic Curve
/// Can either be a `(x, y)` pair or the point at infinity `Inf`
#[derive(PartialEq, Debug)]
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
        let curve = EllipticCurve::new(a, b, g, p);
    }

    #[test]
    #[should_panic(expected = "Singular elliptic curve given")]
    fn test_elliptic_cuve_constructor_singular() {
        // produce toy singular elliptic curve 4a^3 + 3b^2 = 0
        let a = BigUint::new(vec!(11 - 3));
        let b = BigUint::new(vec!(2));
        let g = Point::Pair {x: BigUint::new(vec!(2)), y: BigUint::new(vec!(3)) };
        let p = BigUint::new(vec!(11));
        let curve = EllipticCurve::new(a, b, g, p);
    }

    #[test]
    #[should_panic(expected = "a or b not in GF(p)")]
    fn test_elliptic_cuve_constructor_invalid_a() {
        let a = BigUint::new(vec!(12));
        let b = BigUint::new(vec!(2));
        let g = Point::Pair {x: BigUint::new(vec!(2)), y: BigUint::new(vec!(3)) };
        let p = BigUint::new(vec!(11));
        let curve = EllipticCurve::new(a, b, g, p);
    }
}
