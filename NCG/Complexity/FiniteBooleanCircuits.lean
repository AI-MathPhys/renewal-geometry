/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import Mathlib

/-!
# Finite Boolean circuits and nonuniform circuit families

This file supplies the concrete circuit notions used by the manuscript's
resource-faithful complexity bridge. Circuits are finite formulas over input,
constant, NOT, AND, and OR gates; `circuitSize` is the least gate count of a
circuit computing the given Boolean function. `HasPolynomialCircuits` is the
usual nonuniform polynomial-size condition, stated by an explicit circuit at
every input length.
-/

namespace NCG.Complexity

/-- A finite Boolean circuit/formula on `n` input wires. -/
inductive BooleanCircuit (n : ℕ) where
  | input : Fin n → BooleanCircuit n
  | const : Bool → BooleanCircuit n
  | not : BooleanCircuit n → BooleanCircuit n
  | and : BooleanCircuit n → BooleanCircuit n → BooleanCircuit n
  | or : BooleanCircuit n → BooleanCircuit n → BooleanCircuit n
deriving DecidableEq

/-- Evaluation of a Boolean circuit on one input word. -/
def BooleanCircuit.eval {n : ℕ} :
    BooleanCircuit n → (Fin n → Bool) → Bool
  | .input i, x => x i
  | .const b, _ => b
  | .not c, x => !(c.eval x)
  | .and c d, x => c.eval x && d.eval x
  | .or c d, x => c.eval x || d.eval x

/-- Number of non-input gates in a Boolean circuit. -/
def BooleanCircuit.gateCount {n : ℕ} : BooleanCircuit n → ℕ
  | .input _ => 0
  | .const _ => 1
  | .not c => c.gateCount + 1
  | .and c d => c.gateCount + d.gateCount + 1
  | .or c d => c.gateCount + d.gateCount + 1

/-- A circuit computes a Boolean function when their truth tables agree. -/
def BooleanCircuit.Computes {n : ℕ} (c : BooleanCircuit n)
    (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x, c.eval x = f x

/-- Least gate count of a circuit computing `f`. -/
noncomputable def circuitSize {n : ℕ} (f : (Fin n → Bool) → Bool) : ℕ :=
  sInf {s : ℕ | ∃ c : BooleanCircuit n, c.Computes f ∧ c.gateCount = s}

/-- Any concrete circuit computing `f` bounds its least circuit size. -/
theorem circuitSize_le_gateCount {n : ℕ} (f : (Fin n → Bool) → Bool)
    (c : BooleanCircuit n) (hc : c.Computes f) :
    circuitSize f ≤ c.gateCount := by
  apply Nat.sInf_le
  exact ⟨c, hc, rfl⟩

/-- A length-indexed Boolean language/family. -/
abbrev LanguageFamily := ∀ n : ℕ, (Fin n → Bool) → Bool

/-- Nonuniform polynomial-size circuit families (`P/poly` at the circuit
level). -/
def HasPolynomialCircuits (L : LanguageFamily) : Prop :=
  ∃ C k : ℕ, ∀ n, ∃ c : BooleanCircuit n,
    c.Computes (L n) ∧ c.gateCount ≤ C * (n + 1) ^ k

/-- A numerical function has a polynomial upper bound. -/
def PolynomiallyBounded (f : ℕ → ℕ) : Prop :=
  ∃ C k : ℕ, ∀ n, f n ≤ C * (n + 1) ^ k

/-- A numerical function eventually beats every proposed polynomial bound,
in the pointwise witness form needed by the bridge. -/
def GrowsFasterThanEveryPolynomial (f : ℕ → ℕ) : Prop :=
  ∀ C k : ℕ, ∃ n, C * (n + 1) ^ k < f n

end NCG.Complexity
