module RandomBigInteger

open System
open System.Numerics

let RandomIntegerBelow (rnd : Random) (N : bigint) =
    let bytes = N.ToByteArray ()
    rnd.NextBytes (bytes)
    bytes.[bytes.Length - 1] <- bytes.[bytes.Length - 1] &&& 0x7Fuy //force sign bit to positive
    let mutable R = bigint (bytes)
    while R >= N do
        rnd.NextBytes (bytes)
        bytes.[bytes.Length - 1] <- bytes.[bytes.Length - 1] &&& 0x7Fuy //force sign bit to positive
        R <- bigint (bytes)
    R