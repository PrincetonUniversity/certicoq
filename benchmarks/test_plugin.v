Require Import Arith.
From CertiCoq Require Import CertiCoq.

Definition foo := 3 + 4.

CertiCoq Compile foo.

Require Import Binom.

CertiCoq Compile main.

Require Import CertiCoq.Benchmarks.vs.

CertiCoq Compile main.
