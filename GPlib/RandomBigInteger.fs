module RandomBigInteger

open System
open System.Numerics

let NextBigInteger (rnd : Random) (start : BigInteger, endd : BigInteger) =
    let next (rnd : Random) (bitLength : int) =
        if (bitLength < 1)
        then BigInteger.Zero
        else let bytes = bitLength / 8
             let bits = bitLength % 8
             let bs = [| for i in 0 .. bytes do
                            yield 0uy |] : byte[]
             rnd.NextBytes(bs)
             let mask = byte (0xFF >>> (8 - bits))
             bs.[bs.Length - 1] <- bs.[bs.Length - 1] &&& mask
             BigInteger(bs)
    if (start = endd)
    then start
    else let res = endd
         let (start, endd, res) = 
             if start > endd
             then (res, start, endd - start)
             else (start, endd, res-start)
         let bs = res.ToByteArray()
         let mutable bits = 8
         let mutable mask = 0x7Fuy
         while ((bs.[bs.Length - 1] &&& mask) = bs.[bs.Length - 1]) do
            bits <- bits - 1
            mask <- mask >>> 1
         bits <- bits + 8 * bs.Length
         ((next (rnd : Random) (bits + 1) * res) / BigInteger.Pow(BigInteger 2, bits + 1)) + start

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