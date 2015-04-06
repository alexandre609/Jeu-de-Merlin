Require Import Bool.
Require Import List.
Require Import NArith.
Require Import Omega.

Definition paire_entiers := (nat * nat)%type.
Definition nuplet := (nat * bool) %type.

Inductive plateau : Type := new_plateau :
bool->bool->bool->bool->bool->bool->bool->bool->bool->plateau.




(*Definition plateau : nuplet := (9,true).*)
