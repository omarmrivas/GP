module Algebra

open DataTypes

let div x y : base_type =
    if y = zero
    then one
    else x / y

let mul x y : base_type = x * y

let mk_vector3D x y z : vector3D = V (x,y,z)

let mk_matrix x y z : matrix = M (x,y,z)

let v_add u v =
    match (u,v) with
        V (u1,u2,u3),
        V (v1,v2,v3) -> V (u1+v1, u2+v2, u3+v3)

let v_sub u v =
    match (u,v) with
        V (u1,u2,u3),
        V (v1,v2,v3) -> V (u1-v1, u2-v2, u3-v3)


let dot m n =
    match (m,n) with
        V (a1,a2,a3),
        V (b1,b2,b3) -> a1*b1 + a2*b2 + a3*b3

let cross u v =
    match (u,v) with
        V (u1,u2,u3),
        V (v1,v2,v3) -> V (u2*v3 - u3*v2, u1*v3 - u3*v1, u1*v2 - u2*v1)

let v_norm u =
    match u with
        V (u1,u2,u3) -> sqrt (u1*u1 + u2*u2 + u3*u3)

let m_add m n =
    match (m,n) with
        M (V (a11, a12, a13),
           V (a21, a22, a23),
           V (a31, a32, a33)),
        M (V (b11, b12, b13),
           V (b21, b22, b23),
           V (b31, b32, b33)) ->M (V (a11+b11, a12+b12, a13+b13),
                                   V (a21+b21, a22+b22, a23+b23),
                                   V (a31+b31, a32+b32, a33+b33))

let m_sub m n =
    match (m,n) with
        M (V (a11, a12, a13),
           V (a21, a22, a23),
           V (a31, a32, a33)),
        M (V (b11, b12, b13),
           V (b21, b22, b23),
           V (b31, b32, b33)) ->M (V (a11-b11, a12-b12, a13-b13),
                                   V (a21-b21, a22-b22, a23-b23),
                                   V (a31-b31, a32-b32, a33-b33))


let multiplyM m n =
    match (m,n) with
        M (V (a11, a12, a13),
           V (a21, a22, a23),
           V (a31, a32, a33)),
        M (V (b11, b12, b13),
           V (b21, b22, b23),
           V (b31, b32, b33)) ->
         M (V (a11*b11 + a12 * b21 + a13 * b31, a11*b12 + a12 * b22 + a13 * b32, a11*b13 + a12 * b23 + a13 * b33),
            V (a21*b11 + a22 * b21 + a23 * b31, a21*b12 + a22 * b22 + a23 * b32, a21*b13 + a22 * b23 + a23 * b33),
            V (a31*b11 + a32 * b21 + a33 * b31, a31*b12 + a32 * b22 + a33 * b32, a31*b13 + a32 * b23 + a33 * b33))

let multiplyV m v =
    match (m,v) with
        M (V (a11, a12, a13),
           V (a21, a22, a23),
           V (a31, a32, a33)),
           V(x, y, z) -> V (a11*x + a12 * y + a13 * z,
                            a21*x + a22 * y + a23 * z,
                            a31*x + a32 * y + a33 * z)

let identity : matrix =
    M (V (one, zero, zero),
       V (zero, one, zero),
       V (zero, zero, one))

let translate t = 
    match t with
        V (tx, ty, tz) -> M (V (one, zero, tx),
                             V (zero, one, ty),
                             V (zero, zero, one))

let scale t =
    match t with
        V (sx, sy, sz) -> M (V (sx, zero, zero),
                             V (zero, sy, zero),
                             V (zero, zero, one))

let rotate theta =
    let s = sin theta
    let c = sin theta
    M (V (c, -s, zero),
       V (s, c, zero),
       V (zero, zero, one))

let hrotate theta =
    let s = sinh theta
    let c = cosh theta
    M (V (c, s, zero),
       V (s, c, zero),
       V (zero, zero, one))

let transpose m =
    match m with
        M (V (a11, a12, a13),
           V (a21, a22, a23),
           V (a31, a32, a33)) -> M (V (a11, a21, a31),
                                    V (a12, a22, a32),
                                    V (a13, a23, a33))

let det m = 
    match m with
        M (V (a, b, c),
           V (d, e, f),
           V (g, h, i)) -> a*e*i+b*f*g+c*d*h-c*e*g-b*d*i-a*f*h
