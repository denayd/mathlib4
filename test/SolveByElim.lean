/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Scott Morrison
-/
import Mathlib.Tactic.SolveByElim

def test1 (h : Nat) : Nat := by solveByElim
def test2 {α β : Type} (f : α → β) (a : α) : β := by solveByElim
def test3 {α β : Type} (f : α → α → β) (a : α) : β := by solveByElim
def test4 {α β γ : Type} (f : α → β) (g : β → γ) (a : α) : γ := by solveByElim
def test5 {α β γ : Type} (f : α → β) (g : β → γ) (b : β) : γ := by solveByElim
def test6 {α : Nat → Type} (f : (n : Nat) → α n → α (n+1)) (a : α 0) : α 5 := by solveByElim
