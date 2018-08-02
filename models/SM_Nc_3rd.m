(* SM with Nc colors and 3rd generation fermions only *)
Needs["ARGES`"];

(* Reset ARGES every time reading in this file *)
Reset[];

(* Declare number of gauge groups first *)
NumberOfSubgroups = 3;

(* Specify gauge groups, no GUT normalization *)
Gauge[gy, U, 1, {0, 1, 1}];
Gauge[g, SU, 2, {0, 3, 1}];
Gauge[gs, SU, Nc, {0, 1, Sqr[Nc] - 1}];

(* Specify full fermion sector *)
(* we will define no Yukawas for the first 2 generations later *)
WeylFermion[Q, 3, {+1/6, 2, Nc}];
WeylFermion[L, 3, {-1/2, 2, 1}];
WeylFermion[D, 3, {-1/3, 1, Nc}];
WeylFermion[U, 3, {+2/3, 1, Nc}];
WeylFermion[E, 3, {-1, 1, 1}];

(* Scalar Field with VEV *)
ComplexScalar[H, {1, 1}, {+1/2, 2, 1}];
VEV[v, Re[H], {1, 1}, {1, 2, 1}, 1];

(* Yukawa sector - third generations only *)
Yukawa[ yb, H, adj[Q], D, 
 {1 &, KroneckerDelta[#1, #2] &, KroneckerDelta[#2, #3] &}, 
 (KroneckerDelta[#3, 3] KroneckerDelta[#4, 3])& ];
 
Yukawa[ ytau, H, adj[L], E, 
 {1 &, KroneckerDelta[#1, #2] &, 1 &}, 
 (KroneckerDelta[#3, 3] KroneckerDelta[#4, 3])& ];
 
Yukawa[ yt, adj[H], adj[Q], U, 
 {1 &, Eps[#1, #2] &, KroneckerDelta[#2, #3] &},
 (KroneckerDelta[#3, 3] KroneckerDelta[#4, 3])& ];

(* Quartic coupling ~ -1/2 lamda |phi|^4 *)
ScalarQuartic[\[Lambda], adj[H], H, adj[H], H, 
 {1&, (KroneckerDelta[#1, #2] KroneckerDelta[#3, #4])&, 1&}, 
 (KroneckerDelta[#2, #3] KroneckerDelta[#1, #4] 
  KroneckerDelta[#5, #8] KroneckerDelta[#6, #7])/2 & ];

(* Compute gauge invariants already *)
ComputeInvariants[];
