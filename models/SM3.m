(* Standard Model with 3rd generation Yukawas only *)
Needs["ARGES`"]
Reset[];
NumberOfSubgroups = 3;
Gauge[g1, U, 1, {0, 1, 1}];
Gauge[g2, SU, 2, {0, 3, 1}];
Gauge[g3, SU, 3, {0, 1, 8}];
WeylFermion[Q, 3, { 1/6, 2, 3}];
WeylFermion[L, 3, {-1/2, 2, 1}];
WeylFermion[D, 3, {-1/3, 1, 3}];
WeylFermion[U, 3, {+ 2/3, 1, 3}];
WeylFermion[E, 3, {-1, 1, 1}];
ComplexScalar[H, {1,1}, { +1/2, 2, 1}];
VEV[v, Re[H], {1,1}, {1,2,1}, 1];
Yukawa[yb, H, adj[Q], D, {1 &, KroneckerDelta[#1, #2] &, KroneckerDelta[#2, #3] &}, (KroneckerDelta[#3,3] KroneckerDelta[#4,3])&];
Yukawa[ytau, H, adj[L], E, {1 &, KroneckerDelta[#1, #2] &, 1 &}, (KroneckerDelta[#3,3] KroneckerDelta[#4,3])&];
Yukawa[yt, adj[H], adj[Q], U, {1 &, Eps[#1, #2] &, KroneckerDelta[#2, #3] &}, (KroneckerDelta[#3,3] KroneckerDelta[#4,3])&];
Quartic[\[Lambda], adj[H], H, adj[H], H, {1&, (KroneckerDelta[#1, #2] KroneckerDelta[#3, #4])&, 1&}, 1/2(KroneckerDelta[#2,#3] KroneckerDelta[#1,#4] KroneckerDelta[#5,#8] KroneckerDelta[#6,#7])&];
ScalarMass[\[Mu]2, adj[H], H, {1&, KroneckerDelta[#1,#2]&, 1&}, 1&];
ComputeInvariants[];
