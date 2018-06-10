module Approximation

(*open System
open MathNet.Numerics
open MathNet.Numerics.LinearAlgebra

let two = BigRational.FromInt 2

let br_sqrt i x =
    let x0 = (BigRational.Parse << (fun x -> x + "N" )<< string << sqrt << BigRational.ToDouble) x
    let rec babylonian i xn =
        if i <= 0
        then xn
        else babylonian (i-1) ((xn + x / xn) / two)
    babylonian i x0*)
