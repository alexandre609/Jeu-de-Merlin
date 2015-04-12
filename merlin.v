Require Import Bool.
Require Import List.
Require Import NArith.
Require Import Omega.

Definition plateau := (bool*bool*bool*bool*bool*bool*bool*bool*bool)%type.

Inductive coord_aux : Type :=
| a : coord_aux
| b : coord_aux
| c : coord_aux.

Definition coord := (coord_aux * coord_aux)%type.

Definition partie := (list coord)%type.

Function applique_clic (Plat : plateau) (Coord : coord) : plateau :=
match Coord with
|(a,a)=> match Plat with (A,B,C,D,E,F,G,H,J) => (negb(A),negb(B),C,negb(D), negb(E),F,G,H,J) end
|(a,b)=> match Plat with (A,B,C,D,E,F,G,H,J) => (negb(A),negb(B),negb(C),D, E,F,G,H,J) end
|(a,c)=> match Plat with (A,B,C,D,E,F,G,H,J) => (A,negb(B),negb(C),D, negb(E),negb(F),G,H,J) end
|(b,a)=> match Plat with (A,B,C,D,E,F,G,H,J) => (negb(A),B,C,negb(D), E,F,negb(G),H,J) end
|(b,b)=> match Plat with (A,B,C,D,E,F,G,H,J) => (A,negb(B),C,negb(D), negb(E),negb(F),G,negb(H),J) end
|(b,c)=> match Plat with (A,B,C,D,E,F,G,H,J) => (A,B,negb(C),D, E,negb(F),G,H,negb(J)) end
|(c,a)=> match Plat with (A,B,C,D,E,F,G,H,J) => (A,B,C,negb(D), negb(E),F,negb(G),negb(H),J) end
|(c,b)=> match Plat with (A,B,C,D,E,F,G,H,J) => (A,B,C,D, E,F,negb(G),negb(H),negb(J)) end
|(c,c)=> match Plat with (A,B,C,D,E,F,G,H,J) => (A,B,C,D, negb(E),negb(F),G,negb(H),negb(J)) end
end.

Fixpoint applique_partie
(Plat : plateau) (Part : partie) : plateau :=
match Part with
| Coord :: l => applique_partie (applique_clic Plat Coord) l
| nil => Plat
end.

Definition plateau_init_test : plateau := (false,false,false,false,false,false,false,false,false).

Definition plateau_gagnant (Plat : plateau) : Prop :=
Plat = (true,true,true,true,true,true,true,true,true).

Definition partie_gagnante (Plat : plateau) (Part : partie) : Prop :=
plateau_gagnant(applique_partie Plat Part).

Theorem exists_partie_gagnante_pour_init_test :
    exists p, partie_gagnante plateau_init_test p.
Proof.
exists ((a,a)::(a,c)::(c,c)::(c,a)::(b,b)::nil).
unfold partie_gagnante.
simpl.
unfold plateau_gagnant.
reflexivity.
Qed.

Lemma double_clic : forall (Plat:plateau), forall (Coord : coord),
applique_clic(applique_clic Plat Coord) Coord = Plat.
Proof.
intros.
destruct Plat.
destruct p,p,p,p,p,p,p.
unfold applique_clic.
destruct Coord.
case c0;case c1;rewrite ?negb_involutive;reflexivity.
Qed.


Lemma commut : forall (P:plateau), forall (A B : coord),
applique_clic(applique_clic P A) B = applique_clic(applique_clic P B) A.
Proof.
intros.
destruct P.
destruct p, p, p, p, p, p, p.
destruct A.
destruct B.
unfold applique_clic.
case c0;case c1;case c2;case c3;simpl;trivial.
Qed.

Function change_une_coord (Coord : coord) : partie :=
match Coord with
|(a,a) => (a,a)::(a,b)::(a,c)::(b,a)::(b,b)::(c,a)::nil
|(a,c) => (a,c)::(b,c)::(c,c)::(a,b)::(b,b)::(a,a)::nil
|(c,c) => (c,c)::(c,b)::(c,a)::(b,c)::(b,b)::(a,c)::nil
|(c,a) => (c,a)::(b,a)::(a,a)::(c,b)::(b,b)::(c,c)::nil
|(b,b) => (b,b)::(a,b)::(b,a)::(c,b)::(b,c)::nil
|(b,a) => (b,a)::(a,b)::(a,c)::(c,b)::(c,c)::nil
|(b,c) => (b,c)::(a,b)::(a,a)::(c,b)::(c,a)::nil
|(a,b) => (a,b)::(b,a)::(c,a)::(b,c)::(c,c)::nil
|(c,b) => (c,b)::(b,a)::(a,a)::(b,c)::(a,c)::nil
end.

(*Compute applique_partie plateau_init_test (change_une_coord (a,a)).*)

Fixpoint liste_blanches_aux (Plat : plateau) (n : nat) {struct n} : partie :=
match n, Plat with
| O,  _ => nil
| S p, (true,true,true,true,true,true,true,true,true)         => nil
| S p, (false, a12, a13, a21, a22, a23, a31, a32, a33)        => (a,a)::liste_blanches_aux (true, a12, a13, a21, a22, a23, a31, a32, a33) p
| S p, (true, false, a13, a21, a22, a23, a31, a32, a33)       => (a,b)::liste_blanches_aux (true, true, a13, a21, a22, a23, a31, a32, a33) p
| S p, (true, true, false, a21, a22, a23, a31, a32, a33)      => (a,c)::liste_blanches_aux (true, true, true, a21, a22, a23, a31, a32, a33) p
| S p, (true, true, true, false, a22, a23, a31, a32, a33)     => (b,a)::liste_blanches_aux (true, true, true, true, a22, a23, a31, a32, a33) p
| S p, (true, true, true, true, false, a23, a31, a32, a33)    => (b,b)::liste_blanches_aux (true, true, true, true, true, a23, a31, a32, a33) p
| S p, (true, true, true, true, true, false, a31, a32, a33)   => (b,c)::liste_blanches_aux (true, true, true, true, true, true, a31, a32, a33) p
| S p, (true, true, true, true, true, true, false, a32, a33)  => (c,a)::liste_blanches_aux (true, true, true, true, true, true, true, a32, a33) p
| S p, (true, true, true, true, true, true, true, false, a33) => (c,b)::liste_blanches_aux (true, true, true, true, true, true, true, true, a33) p
| S p, (true, true, true, true, true, true, true, true, false)=> (c,c)::liste_blanches_aux (true, true, true, true, true, true, true, true, true) p
end.

Definition liste_blanches (plateau : plateau) : partie :=
liste_blanches_aux plateau 9.

(*Compute liste_blanches plateau_init_test.*)
Fixpoint strategie_gagnante_pour_liste_des_blanches (liste_des_blanches : partie) := 
match liste_des_blanches with
| nil => nil
| cons first rest => (change_une_coord first) ++ (strategie_gagnante_pour_liste_des_blanches rest)
end.

Fixpoint strategie_gagnante (plateau : plateau) : partie :=
strategie_gagnante_pour_liste_des_blanches (liste_blanches plateau).

Compute strategie_gagnante (false,false,false,false,false,false,false,false,false).
Compute strategie_gagnante (true,true,true,true,true,true,false,false,false).

Lemma coord_eq_dec : forall (x y : coord), {x = y} + {x <> y}.
Proof.
intros.
destruct x, y.
destruct c0, c1, c2, c3;
  try (left; congruence);
  try (right; congruence).
Qed.

Function if_even_then_nil_else_id (Part:partie) (Case:coord) : partie :=
match Part with 
| nil => nil
| _ => if Even.even_odd_dec (count_occ coord_eq_dec Part Case) then nil else Case :: nil
end.

Function partie_simplifiee (Part : partie) : partie :=
   if_even_then_nil_else_id Part (a,a) ++ if_even_then_nil_else_id Part (a,b) ++ if_even_then_nil_else_id Part (a,c)
++ if_even_then_nil_else_id Part (b,a) ++ if_even_then_nil_else_id Part (b,b) ++ if_even_then_nil_else_id Part (b,c)
++ if_even_then_nil_else_id Part (c,a) ++ if_even_then_nil_else_id Part (c,b) ++ if_even_then_nil_else_id Part (c,c).


(*Lemma max_neuf_coups : forall (Part : partie),
(length (partie_simplifiee Part)) <= 9.
Proof.
intros.
induction Part.
unfold partie_simplifiee.
simpl.
omega.
induction Part.
unfold partie_simplifiee.
simpl.
induction (coord_eq_dec a0).
simpl.
apply plus_le_compat.
assumption.
Qed.*)