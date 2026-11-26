import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18729
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

private def circuit : Circuit := ⟨[⟨.or,[5,11]⟩,⟨.or,[3,27]⟩,⟨.or,[2,28]⟩,⟨.and,[15,29]⟩,⟨.or,[6,12]⟩,⟨.or,[4,31]⟩,⟨.or,[3,32]⟩,⟨.and,[16,33]⟩,⟨.or,[9,2]⟩,⟨.or,[7,35]⟩,⟨.or,[6,36]⟩,⟨.and,[19,37]⟩,⟨.or,[10,3]⟩,⟨.or,[8,39]⟩,⟨.or,[7,40]⟩,⟨.and,[20,41]⟩,⟨.or,[11,4]⟩,⟨.or,[9,43]⟩,⟨.or,[8,44]⟩,⟨.and,[21,45]⟩,⟨.or,[12,5]⟩,⟨.or,[10,47]⟩,⟨.or,[9,48]⟩,⟨.and,[22,49]⟩,⟨.or,[46,50]⟩,⟨.or,[42,51]⟩,⟨.or,[38,52]⟩,⟨.or,[34,53]⟩,⟨.or,[30,54]⟩],55⟩
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
private abbrev adj (u v : Fin 13) := u = v ∨ u = v+1 ∨ u = v+3 ∨ u = v+9
private def pair (u v : Fin 13) (i : Fin 26) := decide (i = Fin.castAdd 13 u ∨ i = Fin.natAdd 13 v)
private def input (x : Fin 26 → Bool) := List.ofFn x ++ [x 0 || x 1]
private def value (x : Fin 26 → Bool) := ((x 15 && (x 2 || (x 3 || (x 5 || x 11)))) || ((x 16 && (x 3 || (x 4 || (x 6 || x 12)))) || ((x 19 && (x 6 || (x 7 || (x 9 || x 2)))) || ((x 20 && (x 7 || (x 8 || (x 10 || x 3)))) || ((x 21 && (x 8 || (x 9 || (x 11 || x 4)))) || (x 22 && (x 9 || (x 10 || (x 12 || x 5)))))))))

private theorem evalCircuit (x : Fin 26 → Bool) : circuit.eval (input x) = value x := by
  let w0 : List Bool := [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9,x 10,x 11,x 12,x 13,x 14,x 15,x 16,x 17,x 18,x 19,x 20,x 21,x 22,x 23,x 24,x 25,(x 0 || x 1)]
  have init : input x = w0 := rfl
  let b0 := x 5 || x 11
  let w1 : List Bool := [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9,x 10,x 11,x 12,x 13,x 14,x 15,x 16,x 17,x 18,x 19,x 20,x 21,x 22,x 23,x 24,x 25,(x 0 || x 1),b0]
  have h0 : step w0 ⟨.or,[5,11]⟩ = w1 := by
    change w0 ++ [x 5 || (x 11 || false)] = w1
    rw [Bool.or_false]
    rfl
  let b1 := x 3 || b0
  let w2 : List Bool := [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9,x 10,x 11,x 12,x 13,x 14,x 15,x 16,x 17,x 18,x 19,x 20,x 21,x 22,x 23,x 24,x 25,(x 0 || x 1),b0,b1]
  have h1 : step w1 ⟨.or,[3,27]⟩ = w2 := by
    change w1 ++ [x 3 || (b0 || false)] = w2
    rw [Bool.or_false]
    rfl
  let b2 := x 2 || b1
  let w3 : List Bool := [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9,x 10,x 11,x 12,x 13,x 14,x 15,x 16,x 17,x 18,x 19,x 20,x 21,x 22,x 23,x 24,x 25,(x 0 || x 1),b0,b1,b2]
  have h2 : step w2 ⟨.or,[2,28]⟩ = w3 := by
    change w2 ++ [x 2 || (b1 || false)] = w3
    rw [Bool.or_false]
    rfl
  let b3 := x 15 && b2
  let w4 : List Bool := [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9,x 10,x 11,x 12,x 13,x 14,x 15,x 16,x 17,x 18,x 19,x 20,x 21,x 22,x 23,x 24,x 25,(x 0 || x 1),b0,b1,b2,b3]
  have h3 : step w3 ⟨.and,[15,29]⟩ = w4 := by
    change w3 ++ [x 15 && (b2 && true)] = w4
    rw [Bool.and_true]
    rfl
  let b4 := x 6 || x 12
  let w5 : List Bool := [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9,x 10,x 11,x 12,x 13,x 14,x 15,x 16,x 17,x 18,x 19,x 20,x 21,x 22,x 23,x 24,x 25,(x 0 || x 1),b0,b1,b2,b3,b4]
  have h4 : step w4 ⟨.or,[6,12]⟩ = w5 := by
    change w4 ++ [x 6 || (x 12 || false)] = w5
    rw [Bool.or_false]
    rfl
  let b5 := x 4 || b4
  let w6 : List Bool := [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9,x 10,x 11,x 12,x 13,x 14,x 15,x 16,x 17,x 18,x 19,x 20,x 21,x 22,x 23,x 24,x 25,(x 0 || x 1),b0,b1,b2,b3,b4,b5]
  have h5 : step w5 ⟨.or,[4,31]⟩ = w6 := by
    change w5 ++ [x 4 || (b4 || false)] = w6
    rw [Bool.or_false]
    rfl
  let b6 := x 3 || b5
  let w7 : List Bool := [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9,x 10,x 11,x 12,x 13,x 14,x 15,x 16,x 17,x 18,x 19,x 20,x 21,x 22,x 23,x 24,x 25,(x 0 || x 1),b0,b1,b2,b3,b4,b5,b6]
  have h6 : step w6 ⟨.or,[3,32]⟩ = w7 := by
    change w6 ++ [x 3 || (b5 || false)] = w7
    rw [Bool.or_false]
    rfl
  let b7 := x 16 && b6
  let w8 : List Bool := [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9,x 10,x 11,x 12,x 13,x 14,x 15,x 16,x 17,x 18,x 19,x 20,x 21,x 22,x 23,x 24,x 25,(x 0 || x 1),b0,b1,b2,b3,b4,b5,b6,b7]
  have h7 : step w7 ⟨.and,[16,33]⟩ = w8 := by
    change w7 ++ [x 16 && (b6 && true)] = w8
    rw [Bool.and_true]
    rfl
  let b8 := x 9 || x 2
  let w9 : List Bool := [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9,x 10,x 11,x 12,x 13,x 14,x 15,x 16,x 17,x 18,x 19,x 20,x 21,x 22,x 23,x 24,x 25,(x 0 || x 1),b0,b1,b2,b3,b4,b5,b6,b7,b8]
  have h8 : step w8 ⟨.or,[9,2]⟩ = w9 := by
    change w8 ++ [x 9 || (x 2 || false)] = w9
    rw [Bool.or_false]
    rfl
  let b9 := x 7 || b8
  let w10 : List Bool := [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9,x 10,x 11,x 12,x 13,x 14,x 15,x 16,x 17,x 18,x 19,x 20,x 21,x 22,x 23,x 24,x 25,(x 0 || x 1),b0,b1,b2,b3,b4,b5,b6,b7,b8,b9]
  have h9 : step w9 ⟨.or,[7,35]⟩ = w10 := by
    change w9 ++ [x 7 || (b8 || false)] = w10
    rw [Bool.or_false]
    rfl
  let b10 := x 6 || b9
  let w11 : List Bool := [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9,x 10,x 11,x 12,x 13,x 14,x 15,x 16,x 17,x 18,x 19,x 20,x 21,x 22,x 23,x 24,x 25,(x 0 || x 1),b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10]
  have h10 : step w10 ⟨.or,[6,36]⟩ = w11 := by
    change w10 ++ [x 6 || (b9 || false)] = w11
    rw [Bool.or_false]
    rfl
  let b11 := x 19 && b10
  let w12 : List Bool := [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9,x 10,x 11,x 12,x 13,x 14,x 15,x 16,x 17,x 18,x 19,x 20,x 21,x 22,x 23,x 24,x 25,(x 0 || x 1),b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11]
  have h11 : step w11 ⟨.and,[19,37]⟩ = w12 := by
    change w11 ++ [x 19 && (b10 && true)] = w12
    rw [Bool.and_true]
    rfl
  let b12 := x 10 || x 3
  let w13 : List Bool := [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9,x 10,x 11,x 12,x 13,x 14,x 15,x 16,x 17,x 18,x 19,x 20,x 21,x 22,x 23,x 24,x 25,(x 0 || x 1),b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12]
  have h12 : step w12 ⟨.or,[10,3]⟩ = w13 := by
    change w12 ++ [x 10 || (x 3 || false)] = w13
    rw [Bool.or_false]
    rfl
  let b13 := x 8 || b12
  let w14 : List Bool := [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9,x 10,x 11,x 12,x 13,x 14,x 15,x 16,x 17,x 18,x 19,x 20,x 21,x 22,x 23,x 24,x 25,(x 0 || x 1),b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13]
  have h13 : step w13 ⟨.or,[8,39]⟩ = w14 := by
    change w13 ++ [x 8 || (b12 || false)] = w14
    rw [Bool.or_false]
    rfl
  let b14 := x 7 || b13
  let w15 : List Bool := [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9,x 10,x 11,x 12,x 13,x 14,x 15,x 16,x 17,x 18,x 19,x 20,x 21,x 22,x 23,x 24,x 25,(x 0 || x 1),b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14]
  have h14 : step w14 ⟨.or,[7,40]⟩ = w15 := by
    change w14 ++ [x 7 || (b13 || false)] = w15
    rw [Bool.or_false]
    rfl
  let b15 := x 20 && b14
  let w16 : List Bool := [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9,x 10,x 11,x 12,x 13,x 14,x 15,x 16,x 17,x 18,x 19,x 20,x 21,x 22,x 23,x 24,x 25,(x 0 || x 1),b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15]
  have h15 : step w15 ⟨.and,[20,41]⟩ = w16 := by
    change w15 ++ [x 20 && (b14 && true)] = w16
    rw [Bool.and_true]
    rfl
  let b16 := x 11 || x 4
  let w17 : List Bool := [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9,x 10,x 11,x 12,x 13,x 14,x 15,x 16,x 17,x 18,x 19,x 20,x 21,x 22,x 23,x 24,x 25,(x 0 || x 1),b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16]
  have h16 : step w16 ⟨.or,[11,4]⟩ = w17 := by
    change w16 ++ [x 11 || (x 4 || false)] = w17
    rw [Bool.or_false]
    rfl
  let b17 := x 9 || b16
  let w18 : List Bool := [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9,x 10,x 11,x 12,x 13,x 14,x 15,x 16,x 17,x 18,x 19,x 20,x 21,x 22,x 23,x 24,x 25,(x 0 || x 1),b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16,b17]
  have h17 : step w17 ⟨.or,[9,43]⟩ = w18 := by
    change w17 ++ [x 9 || (b16 || false)] = w18
    rw [Bool.or_false]
    rfl
  let b18 := x 8 || b17
  let w19 : List Bool := [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9,x 10,x 11,x 12,x 13,x 14,x 15,x 16,x 17,x 18,x 19,x 20,x 21,x 22,x 23,x 24,x 25,(x 0 || x 1),b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16,b17,b18]
  have h18 : step w18 ⟨.or,[8,44]⟩ = w19 := by
    change w18 ++ [x 8 || (b17 || false)] = w19
    rw [Bool.or_false]
    rfl
  let b19 := x 21 && b18
  let w20 : List Bool := [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9,x 10,x 11,x 12,x 13,x 14,x 15,x 16,x 17,x 18,x 19,x 20,x 21,x 22,x 23,x 24,x 25,(x 0 || x 1),b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16,b17,b18,b19]
  have h19 : step w19 ⟨.and,[21,45]⟩ = w20 := by
    change w19 ++ [x 21 && (b18 && true)] = w20
    rw [Bool.and_true]
    rfl
  let b20 := x 12 || x 5
  let w21 : List Bool := [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9,x 10,x 11,x 12,x 13,x 14,x 15,x 16,x 17,x 18,x 19,x 20,x 21,x 22,x 23,x 24,x 25,(x 0 || x 1),b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16,b17,b18,b19,b20]
  have h20 : step w20 ⟨.or,[12,5]⟩ = w21 := by
    change w20 ++ [x 12 || (x 5 || false)] = w21
    rw [Bool.or_false]
    rfl
  let b21 := x 10 || b20
  let w22 : List Bool := [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9,x 10,x 11,x 12,x 13,x 14,x 15,x 16,x 17,x 18,x 19,x 20,x 21,x 22,x 23,x 24,x 25,(x 0 || x 1),b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16,b17,b18,b19,b20,b21]
  have h21 : step w21 ⟨.or,[10,47]⟩ = w22 := by
    change w21 ++ [x 10 || (b20 || false)] = w22
    rw [Bool.or_false]
    rfl
  let b22 := x 9 || b21
  let w23 : List Bool := [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9,x 10,x 11,x 12,x 13,x 14,x 15,x 16,x 17,x 18,x 19,x 20,x 21,x 22,x 23,x 24,x 25,(x 0 || x 1),b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16,b17,b18,b19,b20,b21,b22]
  have h22 : step w22 ⟨.or,[9,48]⟩ = w23 := by
    change w22 ++ [x 9 || (b21 || false)] = w23
    rw [Bool.or_false]
    rfl
  let b23 := x 22 && b22
  let w24 : List Bool := [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9,x 10,x 11,x 12,x 13,x 14,x 15,x 16,x 17,x 18,x 19,x 20,x 21,x 22,x 23,x 24,x 25,(x 0 || x 1),b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16,b17,b18,b19,b20,b21,b22,b23]
  have h23 : step w23 ⟨.and,[22,49]⟩ = w24 := by
    change w23 ++ [x 22 && (b22 && true)] = w24
    rw [Bool.and_true]
    rfl
  let b24 := b19 || b23
  let w25 : List Bool := [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9,x 10,x 11,x 12,x 13,x 14,x 15,x 16,x 17,x 18,x 19,x 20,x 21,x 22,x 23,x 24,x 25,(x 0 || x 1),b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16,b17,b18,b19,b20,b21,b22,b23,b24]
  have h24 : step w24 ⟨.or,[46,50]⟩ = w25 := by
    change w24 ++ [b19 || (b23 || false)] = w25
    rw [Bool.or_false]
    rfl
  let b25 := b15 || b24
  let w26 : List Bool := [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9,x 10,x 11,x 12,x 13,x 14,x 15,x 16,x 17,x 18,x 19,x 20,x 21,x 22,x 23,x 24,x 25,(x 0 || x 1),b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16,b17,b18,b19,b20,b21,b22,b23,b24,b25]
  have h25 : step w25 ⟨.or,[42,51]⟩ = w26 := by
    change w25 ++ [b15 || (b24 || false)] = w26
    rw [Bool.or_false]
    rfl
  let b26 := b11 || b25
  let w27 : List Bool := [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9,x 10,x 11,x 12,x 13,x 14,x 15,x 16,x 17,x 18,x 19,x 20,x 21,x 22,x 23,x 24,x 25,(x 0 || x 1),b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16,b17,b18,b19,b20,b21,b22,b23,b24,b25,b26]
  have h26 : step w26 ⟨.or,[38,52]⟩ = w27 := by
    change w26 ++ [b11 || (b25 || false)] = w27
    rw [Bool.or_false]
    rfl
  let b27 := b7 || b26
  let w28 : List Bool := [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9,x 10,x 11,x 12,x 13,x 14,x 15,x 16,x 17,x 18,x 19,x 20,x 21,x 22,x 23,x 24,x 25,(x 0 || x 1),b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16,b17,b18,b19,b20,b21,b22,b23,b24,b25,b26,b27]
  have h27 : step w27 ⟨.or,[34,53]⟩ = w28 := by
    change w27 ++ [b7 || (b26 || false)] = w28
    rw [Bool.or_false]
    rfl
  let b28 := b3 || b27
  let w29 : List Bool := [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9,x 10,x 11,x 12,x 13,x 14,x 15,x 16,x 17,x 18,x 19,x 20,x 21,x 22,x 23,x 24,x 25,(x 0 || x 1),b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16,b17,b18,b19,b20,b21,b22,b23,b24,b25,b26,b27,b28]
  have h28 : step w28 ⟨.or,[30,54]⟩ = w29 := by
    change w28 ++ [b3 || (b27 || false)] = w29
    rw [Bool.or_false]
    rfl
  change (List.foldl step (input x) [⟨.or,[5,11]⟩,⟨.or,[3,27]⟩,⟨.or,[2,28]⟩,⟨.and,[15,29]⟩,⟨.or,[6,12]⟩,⟨.or,[4,31]⟩,⟨.or,[3,32]⟩,⟨.and,[16,33]⟩,⟨.or,[9,2]⟩,⟨.or,[7,35]⟩,⟨.or,[6,36]⟩,⟨.and,[19,37]⟩,⟨.or,[10,3]⟩,⟨.or,[8,39]⟩,⟨.or,[7,40]⟩,⟨.and,[20,41]⟩,⟨.or,[11,4]⟩,⟨.or,[9,43]⟩,⟨.or,[8,44]⟩,⟨.and,[21,45]⟩,⟨.or,[12,5]⟩,⟨.or,[10,47]⟩,⟨.or,[9,48]⟩,⟨.and,[22,49]⟩,⟨.or,[46,50]⟩,⟨.or,[42,51]⟩,⟨.or,[38,52]⟩,⟨.or,[34,53]⟩,⟨.or,[30,54]⟩]).getD 55 false = value x
  rw [init]
  simp only [List.foldl_cons,List.foldl_nil,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28]
  rfl

private theorem positive : ∀ u v : Fin 13, v ∈ ([2, 3, 6, 7, 8, 9] : List (Fin 13)) → adj u v → value (pair u v) = true := by decide +kernel

private theorem sound (x : Fin 26 → Bool) (hx : value x = true) :
    ∃ u v : Fin 13, adj u v ∧ x (Fin.castAdd 13 u) = true ∧ x (Fin.natAdd 13 v) = true := by
  simp only [value,Bool.or_eq_true,Bool.and_eq_true] at hx
  rcases hx with h | h | h | h | h | h
  · obtain ⟨right,left⟩ := h
    rcases left with h | h | h | h
    · exact ⟨2,2,by decide,h,right⟩
    · exact ⟨3,2,by decide,h,right⟩
    · exact ⟨5,2,by decide,h,right⟩
    · exact ⟨11,2,by decide,h,right⟩
  · obtain ⟨right,left⟩ := h
    rcases left with h | h | h | h
    · exact ⟨3,3,by decide,h,right⟩
    · exact ⟨4,3,by decide,h,right⟩
    · exact ⟨6,3,by decide,h,right⟩
    · exact ⟨12,3,by decide,h,right⟩
  · obtain ⟨right,left⟩ := h
    rcases left with h | h | h | h
    · exact ⟨6,6,by decide,h,right⟩
    · exact ⟨7,6,by decide,h,right⟩
    · exact ⟨9,6,by decide,h,right⟩
    · exact ⟨2,6,by decide,h,right⟩
  · obtain ⟨right,left⟩ := h
    rcases left with h | h | h | h
    · exact ⟨7,7,by decide,h,right⟩
    · exact ⟨8,7,by decide,h,right⟩
    · exact ⟨10,7,by decide,h,right⟩
    · exact ⟨3,7,by decide,h,right⟩
  · obtain ⟨right,left⟩ := h
    rcases left with h | h | h | h
    · exact ⟨8,8,by decide,h,right⟩
    · exact ⟨9,8,by decide,h,right⟩
    · exact ⟨11,8,by decide,h,right⟩
    · exact ⟨4,8,by decide,h,right⟩
  · obtain ⟨right,left⟩ := h
    rcases left with h | h | h | h
    · exact ⟨9,9,by decide,h,right⟩
    · exact ⟨10,9,by decide,h,right⟩
    · exact ⟨12,9,by decide,h,right⟩
    · exact ⟨5,9,by decide,h,right⟩

end PEqualNP.Outside.L_meta_18729

open PEqualNP.Outside.L_meta_18729 in
theorem PEqualNP.Outside.L_meta_18729 : have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Fin (26 : ℕ) → Bool := fun (x2 x3 : Fin (13 : ℕ)) (x4 : Fin (26 : ℕ)) => Decidable.decide (x4 = Fin.castAdd (13 : ℕ) x2 ∨ x4 = Fin.natAdd (13 : ℕ) x3); have x3 : (Fin (26 : ℕ) → Bool) → List Bool := fun (x3 : Fin (26 : ℕ) → Bool) => List.ofFn x3 ++ [x3 (0 : Fin (26 : ℕ)) || x3 (1 : Fin (26 : ℕ))]; ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), x4.size ≤ (29 : ℕ) ∧ (27 : ℕ) ≤ x4.output ∧ x4.output < (27 : ℕ) + x4.size ∧ PEqualNP.TopForm.IsAO2 (27 : ℕ) x4 ∧ (∀ x5 ∈ x4.gates, x5.inputs.Nodup) ∧ (∀ (x5 x6 : Fin (13 : ℕ)), x6 ∈ [(2 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (6 : Fin (13 : ℕ)), (7 : Fin (13 : ℕ)), (8 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))] → x1 x5 x6 → x4.eval (x3 (x2 x5 x6)) = Bool.true) ∧ ∀ (x5 : Fin (26 : ℕ) → Bool), x4.eval (x3 x5) = Bool.true → ∃ (x7 : Fin (13 : ℕ)) (x8 : Fin (13 : ℕ)), x1 x7 x8 ∧ x5 (Fin.castAdd (13 : ℕ) x7) = Bool.true ∧ x5 (Fin.natAdd (13 : ℕ) x8) = Bool.true := by
  refine ⟨circuit,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,?_,?_⟩
  · intro u v hv he
    exact (evalCircuit (pair u v)).trans (positive u v hv he)
  · intro x h
    exact sound x ((evalCircuit x).symm.trans h)
