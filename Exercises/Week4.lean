/-
In this file, you will solve the following riddle:

  Show that a 10×10 board cannot be tiled with dominos in such a way
  that exactly half of the dominos are horizontal and half are vertical.

The idea of the proof is as follows.
Color the columns alternately with white and black.
Each horizontal domino includes a white square and a black square,
while both squares of a vertical domino have the same color.
Since there are 50 dominos in total, a tiling which contains an equal number
of horizontal and vertical dominos would have 25 horizontal dominos.
The horizontal dominos cover 25 white squares and 25 black squares.
The vertical dominos cover an even number of each.
Hence the total number of white squares should be odd.
However, there are 50 white squares, so we reach a contradiction.

The actual proof is slightly different (we color a square with the
index of the column mod 2), but is otherwise very similar.
-/

import Mathlib.Tactic

noncomputable section
open Classical Finset

variable {n m : ℕ}

-- Definition of domino tiling

@[ext]
structure Point where
  x : ℕ
  y : ℕ
deriving Repr

inductive Domino
| H (lft : Point)
| V (top : Point)
deriving Repr

def cells : Domino → Finset Point
| Domino.H lft => { ⟨lft.x, lft.y⟩, ⟨lft.x + 1, lft.y⟩ }
| Domino.V top => { ⟨top.x, top.y⟩, ⟨top.x, top.y + 1⟩ }

def board (n m : ℕ) : Finset Point :=
  map ⟨fun xy => ⟨xy.1, xy.2⟩, by simp [Function.Injective]⟩
    (range n ×ˢ range m)

structure DominoTiling (n m : ℕ) where
  tiles : Finset Domino
  disjoint : Set.PairwiseDisjoint tiles (cells ·)
  union : tiles.disjiUnion (cells ·) disjoint = board n m

-- Lemmas about cardinalities

lemma card_domino (domino : Domino) : #(cells domino) = 2 := by
  sorry

lemma card_board : #(board n m) = n * m := by
  sorry

lemma card_tiling (tiling : DominoTiling n m) :
  2 * #tiling.tiles = n * m := by
  sorry

-- Classification of dominos

def horizontal : Domino → Prop
| Domino.H _ => True
| Domino.V _ => False

def vertical : Domino → Prop
| Domino.H _ => False
| Domino.V _ => True

lemma disjoint_hv : Disjoint (horizontal · : Domino → Prop) (vertical ·) := by
  sorry

lemma either_hv : ∀ x, horizontal x ∨ vertical x := by
  sorry

-- Decomposition of tiling into horizontal and vertical parts

def htiles (tiling : DominoTiling n m) : Finset Domino :=
  tiling.tiles.filter (horizontal ·)

def vtiles (tiling : DominoTiling n m) : Finset Domino :=
  tiling.tiles.filter (vertical ·)

-- use disjoint_filter_filter'
lemma disjoint_hvtiles (tiling : DominoTiling n m) :
  Disjoint (htiles tiling) (vtiles tiling) := by
  sorry

-- use disjUnion_eq_union to start
lemma union_hvtiles (tiling : DominoTiling n m) :
  disjUnion (htiles tiling) (vtiles tiling) (disjoint_hvtiles tiling) = tiling.tiles := by
  sorry

lemma card_hvtiles (tiling : DominoTiling n m) :
  #(htiles tiling) + #(vtiles tiling) = #tiling.tiles := by
  sorry

-- Lemmas for the main theorem

lemma x_sum_board :
  ∑ pt ∈ board n m, pt.x = n*(n-1)/2 * m := by
  calc
    ∑ pt ∈ board n m, pt.x =
      ∑ pt ∈ range n ×ˢ range m, pt.1 := by
      sorry
    _ = ∑ x ∈ range n, ∑ y ∈ range m, x := by
      sorry
    _ = ∑ y ∈ range m, ∑ x ∈ range n, x := by
      sorry
    _ = ∑ y ∈ range m, n*(n-1)/2 := by
      sorry
    _ = #(range m) * (n*(n-1)/2) := by
      sorry
    _ = (n*(n-1)/2) * m := by
      sorry

lemma x_parity_tiling (tiling : DominoTiling n m) :
  n*(n-1)/2*m ≡ #(htiles tiling) [MOD 2] := by
  calc
    n*(n-1)/2*m % 2 = (∑ pt ∈ board n m, pt.x % 2) % 2 := by
      sorry
    _ = (∑ tile ∈ tiling.tiles, ∑ pt ∈ cells tile, pt.x % 2) % 2 := by
      sorry
    _ = (∑ tile ∈ tiling.tiles, (∑ pt ∈ cells tile, pt.x % 2) % 2) % 2 := by
      sorry
    _ = (∑ tile ∈ tiling.tiles, (∑ pt ∈ cells tile, pt.x) % 2) % 2 := by
      sorry
    _ = ((∑ tile ∈ htiles tiling, (∑ pt ∈ cells tile, pt.x) % 2) +
      (∑ tile ∈ vtiles tiling, (∑ pt ∈ cells tile, pt.x) % 2)) % 2 := by
      sorry
    _ = ((∑ tile ∈ htiles tiling, 1) + (∑ tile ∈ vtiles tiling, 0)) % 2 := by
      -- use congr! with [enough names]
      sorry
    _ = (∑ i ∈ htiles tiling, 1) % 2 := by
      sorry
    _ = #(htiles tiling) % 2 := by
      sorry

-- Main theorem

theorem puzzle (tiling : DominoTiling 10 10) :
  #(htiles tiling) ≠ #(vtiles tiling) := by
  by_contra
  have card_htiles : #(htiles tiling) = 25 := by
    sorry
  have := x_parity_tiling tiling
  sorry
