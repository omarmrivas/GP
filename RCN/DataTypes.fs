module DataTypes

open System

type base_type = double
let zero = 0.0
let one = 1.0
let two = 2.0
let three = 3.0

let sin  : base_type -> base_type = Math.Sin
let cos  : base_type -> base_type = Math.Cos
let sinh : base_type -> base_type = Math.Sinh
let cosh : base_type -> base_type = Math.Cosh
let log  : base_type -> base_type = Math.Log
let exp  : base_type -> base_type = Math.Exp

let to_base = double : int -> base_type

type vector2D = base_type * base_type

[<Serializable>]
type vector3D = V of base_type * base_type * base_type

[<Serializable>]
type matrix = M of vector3D * vector3D * vector3D

[<Serializable>]
type Vertex = vector2D

[<Serializable>]
type Edge = Vertex * Vertex

[<Serializable>]
type Quadrilateral = Vertex * Vertex * Vertex * Vertex

