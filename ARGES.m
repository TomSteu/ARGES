BeginPackage["ARGES`"];
	Gauge::usage = "Specify gauge subgroup by Gauge[coupling, Group[N], {Representation1, ...}];";
	WeylFermion::usage = "Add Weyl fermion by WeylFermion[symbol, Flavors, {Representation1, ...}]";
	RealScalar::usage = "Add real scalar by RealScalar[symbol, Flavors, {Representation1, ...}]";
	ComplexScalar::usage = "Add complex scalar by ComplexScalar[Symbol, Flavors, {Representation1, ...}]; this adds the real scalars Re[Symbol] and Im[Symbol]";
	YukawaYaij::usage = "Add Yukawa matrix term (with h.c.) YukawaYaij[Symbol, ScalarField, LeftFermion, RightFermion, {List of contractions for each gauge}]; Contractions are functions [ScalarIndex, LeftFermionIndex, RightFermionIndex], example: Yaijk[y, S, F1, F2, ...] == - y adj[F1].S.F2 + h.c.";
	\[Beta]::usage = "Display Beta function for gauge coupling \[Beta][Gauge, LoopLevel];";
	Reset::usage = "reset/initiate package";
	ComputeInvariants::usage = "Calculates known invariants for beta functions, saves them as rules in subInvariants";
	subInvariants::usage = "containts replacement rules for beta function invariants, use ComputeInvariants[] to calculate";
	GetGauge::usage = "Returns representation / charge for particle"
	F::usage = "fermionic";
	S::usage = "scalar";
	Y::usage = "Yukawa";
	d::usage="Dimension of Representation";
	C2::usage = "Casimir Invariant";
	S2::usage = "Dynkin Index";
	Y2::usage = "Yukawa Invariant";
	Y4::usage = "Yukawa Invariant";
	prod::usage = "product of flavour matrices";
	adj::usage = "adjoint";
	tr::usage = "trace of flavour matrices";
	U::usage = "Unitary Group";
	SU::usage = "Special Unitary Group";
	
	Sqr[x_] := x*x;
	subAlpha = {\[Alpha][g_] -> Sqr[g/(4 \[Pi])]};
	NumberOfSubgroups = 1;

	
	(*Begin["Private`"];*)
		Reset[] := Module[
			{},
			ListGauge = {};
			ListYukawa = {};
			ListQuartic = {};
			WeylFermionList = {};
			RealScalarList = {};
			ComplexScalarList = {};
			subInvariants = {};
			$Assumptions = Element[KroneckerDelta[___], Reals];
		];

		
		Gauge[sym_, group_, n_, reps_List] := Module[
			{},
			If[Dimensions[reps][[1]] != NumberOfSubgroups,
				Message[Gauge::RepMismatch];,
				If[!NumberQ[n], $Assumptions=$Assumptions&&(n>1)&&Element[n,Integers]];
				ListGauge = Append[ListGauge, {sym, group, n, reps}];

			];
		];
		
		GetGauge[part_, gauge_] := Module[
			{posP, posG},
			posG = Position[ListGauge,_List?(#[[1]] == gauge &)];
			If[posG == {}, Return[0];];
			posG = posG[[1,1]];
			posP = Position[ComplexScalarList, part];
			If[posP != {},
				posP = Position[RealScalarList,_List?(#[[1]] == Re[part] &)];,
				posP = Position[RealScalarList,_List?(#[[1]] == part &)];
			];
			If[posP != 0,
				Return[RealScalarList[[posP[[1,1]], 3, posG]]];
			];
			posP = Position[WeylFermionList,_List?(#[[1]] == part &)];
			If[posP != 0,
				Return[WeylFermionList[[posP[[1,1]], 3, posG]]];
			];
			Return[0];
		];
		
		WeylFermion[sym_, Nflavor_, Gauge_List] := Module[
			{},
			If[Dimensions[Gauge][[1]] != NumberOfSubgroups, 
				Message[WeylFermion::RepMismatch];,
				If[!NumberQ[Nflavor], $Assumptions=$Assumptions&&Element[Nflavor,Integers]&&(Nflavor>=0)];
				WeylFermionList = Append[WeylFermionList, {sym, Nflavor, Gauge}];
			];
		];
		
		RealScalar[sym_, Nflavor_, Gauge_List] := Module[
			{},
			If[Dimensions[Gauge][[1]] != NumberOfSubgroups, 
				Message[RealScalar::RepMismatch];,
				If[!NumberQ[Nflavor], $Assumptions=$Assumptions&&Element[Nflavor,Integers]&&(Nflavor>=0)];
				RealScalarList = Append[RealScalarList, {sym, Nflavor, Gauge}];
			];
		];
		
		ComplexScalar[sym_, Nflavor_, Gauge_List] := Module[
			{},
			ComplexScalarList = Append[ComplexScalarList, sym];
			RealScalar[Re[sym], Nflavor, Gauge];
			RealScalar[Im[sym], Nflavor, Gauge];
		];
		
		YukawaYaij[sym_, Sa_, Fi_, Fj_, gauge_List, fak_:1] := Module[
			{posS, posFi, posFj},
			If[Dimensions[gauge][[1]] != NumberOfSubgroups,
				Message[Yukawa::ContractionError];
				Return[];
			];
			posS  = Position[ComplexScalarList, Sa];
			If[posS != {},
				YukawaYaij[sym, Re[Sa], Fi, Fj, gauge, fak/Sqrt[2]];
				YukawaYaij[sym, Im[Sa], Fi, Fj, gauge, I fak/Sqrt[2]];
				Return[];
			];
			posS  = Position[adj/@ComplexScalarList, Sa];
			If[posS != {},
				YukawaYaij[sym, Re[Sa[[1]]], Fi, Fj, gauge, fak/Sqrt[2]];
				YukawaYaij[sym, Im[Sa[[1]]], Fi, Fj, gauge, -I fak/Sqrt[2]];
				Return[];
			];
			posS  = Position[RealScalarList,_List?(#[[1]] == Sa &)];
			posFi = Position[WeylFermionList,_List?(#[[1]] == Fi &)];
			posFj = Position[WeylFermionList,_List?(#[[1]] == Fj &)];
			If[posS == {} || posFi == {} || posFj == {},
				Message[Yukawa::UnknownParticle];,
				ListYukawa = Append[ListYukawa,{sym, posS[[1,1]], posFi[[1,1]], posFj[[1,1]], gauge, (fak KroneckerDelta[#2,1] KroneckerDelta[#3,1])&}];
			];
		];
		
		Quartic\[Lambda]abcd[sym_, Sa_, Sb_, Sc_, Sd_, gauge_List, fak_:(1&)] := Module[
			{posA, posB, posC, posD},
			posA = Position[ComplexScalarList, Sa];
			If[posA != {},
				Quartic\[Lambda]abcd[sym, Re[Sa], Sb, Sc, Sd, gauge, (1/Sqrt[2] fak[#1,#2,#3,#4])&];
				Quartic\[Lambda]abcd[sym, Im[Sa], Sb, Sc, Sd, gauge, (I/Sqrt[2] fak[#1,#2,#3,#4])&];
				Return[];
			];
			posA = Position[adj/@ComplexScalarList, Sa];
			If[posA != {},
				Quartic\[Lambda]abcd[sym, Re[Sa[[1]]], Sb, Sc, Sd, gauge, (1/Sqrt[2] fak[#1,#2,#3,#4])&];
				Quartic\[Lambda]abcd[sym, Im[Sa[[1]]], Sb, Sc, Sd, gauge, (-I/Sqrt[2] fak[#1,#2,#3,#4])&];
				Return[];
			];
			posB = Position[ComplexScalarList, Sb];
			If[posB != {},
				Quartic\[Lambda]abcd[sym, Sa, Re[Sb], Sc, Sd, gauge, (1/Sqrt[2] fak[#1,#2,#3,#4])&];
				Quartic\[Lambda]abcd[sym, Sa, Im[Sb], Sc, Sd, gauge, (I/Sqrt[2] fak[#1,#2,#3,#4])&];
				Return[];
			];
			posB = Position[adj/@ComplexScalarList, Sb];
			If[posB != {},
				Quartic\[Lambda]abcd[sym, Sa, Re[Sb[[1]]], Sc, Sd, gauge, (1/Sqrt[2] fak[#1,#2,#3,#4])&];
				Quartic\[Lambda]abcd[sym, Sa, Im[Sb[[1]]], Sc, Sd, gauge, (-I/Sqrt[2] fak[#1,#2,#3,#4])&];
				Return[];
			];
			posC = Position[ComplexScalarList, Sc];
			If[posC != {},
				Quartic\[Lambda]abcd[sym, Sa, Sb, Re[Sc], Sd, gauge, (1/Sqrt[2] fak[#1,#2,#3,#4])&];
				Quartic\[Lambda]abcd[sym, Sa, Sb, Im[Sc], Sd, gauge, (I/Sqrt[2] fak[#1,#2,#3,#4])&];
				Return[];
			];
			posC = Position[adj/@ComplexScalarList, Sc];
			If[posC != {},
				Quartic\[Lambda]abcd[sym, Sa, Sb, Re[Sc[[1]]], Sd, gauge, (1/Sqrt[2] fak[#1,#2,#3,#4])&];
				Quartic\[Lambda]abcd[sym, Sa, Sb, Im[Sc[[1]]], Sd, gauge, (-I/Sqrt[2] fak[#1,#2,#3,#4])&];
				Return[];
			];
			posD = Position[ComplexScalarList, Sd];
			If[posD != {},
				Quartic\[Lambda]abcd[sym, Sa, Sb, Sc, Re[Sd], gauge, (1/Sqrt[2] fak[#1,#2,#3,#4])&];
				Quartic\[Lambda]abcd[sym, Sa, Sb, Sc, Im[Sd], gauge, (I/Sqrt[2] fak[#1,#2,#3,#4])&];
				Return[];
			];
			posD = Position[adj/@ComplexScalarList, Sd];
			If[posD != {},
				Quartic\[Lambda]abcd[sym, Sa, Sb, Sc, Re[Sd[[1]]], gauge, (1/Sqrt[2] fak[#1,#2,#3,#4])&];
				Quartic\[Lambda]abcd[sym, Sa, Sb, Sc, Im[Sd[[1]]], gauge, (-I/Sqrt[2] fak[#1,#2,#3,#4])&];
				Return[];
			];
			posA = Position[RealScalarList,_List?(#[[1]] == Sa &)];
			posB = Position[RealScalarList,_List?(#[[1]] == Sb &)];
			posC = Position[RealScalarList,_List?(#[[1]] == Sc &)];
			posD = Position[RealScalarList,_List?(#[[1]] == Sd &)];
			If[posA == {} || posB == {} || posC == {} || posD == {},
				Message[Quartic::UnknownParticle];,
				If[Dimensions[gauge][[1]] != NumberOfSubgroups,
					Message[Quartic::ContractionError];,
					ListQuartic = Append[ListQuartic, {sym, posA[[1,1]], posB[[1,1]], posC[[1,1]], posD[[1,1]], gauge, fak}];
				];
			];
		];
		
		\[Beta][\[Alpha][sym_], loop_] := Module[
			{pos},
			pos = Position[ListGauge,_List?(#[[1]] == sym &)];
			If[pos != {}, 
				Return[BetaGauge[pos[[1,1]], loop]];
			];
			Return[0];
		];
		
		\[Beta][sym_, loop_] := Module[
			{pos},
			pos = Position[ListGauge,_List?(#[[1]] == sym &)];
			If[pos != {}, 
				Return[Expand[(\[Beta][\[Alpha][sym], loop] Sqr[4 Pi]/(2 sym))//.subAlpha]];
			];
		];
		
		BetaGauge[pos_, 0] := \[Alpha][ListGauge[[pos,1]]];
		
		BetaGauge[pos_, 1] := Module[
			{beta,x},
			beta = 0;
			beta = beta - 22/3 Sqr[\[Alpha][ListGauge[[pos,1]]]] C2[ListGauge[[pos,1]]]; 
			beta = beta + 4/3 Sqr[\[Alpha][ListGauge[[pos,1]]]] FSum[Hold[S2[WeylFermionList[[#,1]],ListGauge[[pos,1]]]]];
			beta = beta + 1/3 Sqr[\[Alpha][ListGauge[[pos,1]]]] SSum[Hold[S2[RealScalarList[[#,1]], ListGauge[[pos,1]]]]];
			Return[beta];
		];
		
		BetaGauge[pos_, 2] := Module[
			{beta,f,s},
			beta = 0;
			beta = beta - 2 Sqr[\[Alpha][ListGauge[[pos,1]]]] Y4[F,ListGauge[[pos, 1]]]/Sqr[4 Pi];
			beta = beta - 68/3 Power[\[Alpha][ListGauge[[pos,1]]], 3] Sqr[C2[ListGauge[[pos,1]]]];
			beta = beta + Sqr[\[Alpha][ListGauge[[pos,1]]]] FSum[Hold[(Sum[4 \[Alpha][ListGauge[[i,1]]] C2[WeylFermionList[[#,1]], ListGauge[[i,1]]],{i,1,NumberOfSubgroups}] + 20/3 \[Alpha][ListGauge[[pos,1]]] C2[ListGauge[[pos,1]]])S2[WeylFermionList[[#,1]], ListGauge[[pos,1]]]]];
			beta = beta + Sqr[\[Alpha][ListGauge[[pos,1]]]] SSum[Hold[(Sum[4 \[Alpha][ListGauge[[i,1]]] C2[RealScalarList[[#,1]], ListGauge[[i,1]]],{i,1,NumberOfSubgroups}] + 2/3 \[Alpha][ListGauge[[pos,1]]] C2[ListGauge[[pos,1]]])S2[RealScalarList[[#,1]], ListGauge[[pos,1]]]]];
			Return[beta];
		];
		
		BetaYukawa[pa_, pi_, pj_, la_, li_, lj_, 0] := YukawaProd[Yuk[pa], pi, pj, li, lj, la];
		
		BetaYukawa[ pa_, pi_, pj_, la_, li_, lj_, 1] := Module[
			{beta, ss, ii, x, x2, x3, sumIdx},
			beta = 0;
			beta = beta + 1/2 Sum[YukawaProd[Yuk[ss], adj[Yuk[ss]], Yuk[pa], pi, pj, li, lj, Function[{x},(KroneckerDelta[#1, #2]KroneckerDelta[#3, la[[x]]])&]/@Range[NumberOfSubgroups+1]], {ss, 1, SNumber[]}];
			beta = beta + 1/2 Sum[YukawaProd[Yuk[pa], adj[Yuk[ss]], Yuk[ss], pi, pj, li, lj, Function[{x},(KroneckerDelta[#2, #3]KroneckerDelta[#1, la[[x]]])&]/@Range[NumberOfSubgroups+1]], {ss, 1, SNumber[]}];
			beta = beta + 2 Sum[YukawaProd[Yuk[ss], adj[Yuk[pa]], Yuk[ss], pi, pj, li, lj, Function[{x},(KroneckerDelta[#1, #3]KroneckerDelta[#2, la[[x]]])&]/@Range[NumberOfSubgroups+1]], {ss, 1, SNumber[]}];
			beta = beta + 1/2 Sum[Sum@@Join[{(YukawaTrace[adj[Yuk[pa]], Yuk[ss], Function[{x}, (KroneckerDelta[#1, la[[x+1]]] KroneckerDelta[#2, sumIdx[x]])&]/@Range[0,NumberOfSubgroups]] + YukawaTrace[adj[Yuk[ss]], Yuk[pa], Function[{x}, (KroneckerDelta[#2, la[[x+1]]] KroneckerDelta[#1, sumIdx[x]])&]/@Range[0,NumberOfSubgroups]])  Times@@(Function[{x2}, If[x2==0, (ReleaseHold[(Yuk[pa][pi, pj]//.subYuk)][[1,1]][li[[1]], lj[[1]]])(ReleaseHold[(Yuk[pa][pi, pj]//.subYuk)][[1,2]][la[[1]], li[[1]], lj[[1]]]), ReleaseHold[(Yuk[pa][pi, pj]//.subYuk)][[x2+1,1]][sumIdx[x2], li[[x2+1]], lj[[x2+1]]]]]/@Range[0,NumberOfSubgroups])}, Function[{x3},If[x3==0, {sumIdx[0], 1, RealScalarList[[ss,2]]},{sumIdx[x3], 1, If[ListGauge[[x3, 3]] == 1, 1, RealScalarList[[1, 3, x3]]]}]]/@Range[0,NumberOfSubgroups]], {ss, 1, SNumber[]}]/.tr[adj[a_],b_]->tr[b,adj[a]];
			beta = beta - 3 Sum[Sqr[ListGauge[[ii,1]]] (YukawaProd[C2[F, ii], Yuk[pa], pi, pj, li, lj, Function[{x},(KroneckerDelta[#1,1] KroneckerDelta[#2,la[[x]]])&]/@Range[NumberOfSubgroups+1]] + YukawaProd[Yuk[pa], C2[F, ii], pi, pj, li, lj, Function[{x2},(KroneckerDelta[#2,1] KroneckerDelta[#1,la[[x2]]])&]/@Range[NumberOfSubgroups+1]]), {ii, 1, NumberOfSubgroups}]/.{prod[a___, C2[b___], c___][d___]->C2[b] prod[a,c][d]}//.subProd;
			Return[beta/Sqr[4\[Pi]]];
		];
		
		BetaQuartic[a_, b_, c_, d_, la_, lb_, lc_, ld_, 0] := Module[
			{pa, pb, pc, pd, q},
			pa = Join[{a}, la];
			pb = Join[{b}, lb];
			pc = Join[{c}, lc];
			pd = Join[{d}, ld];
			Return[
				ReleaseHold[(Quartic[pa[[1]],pb[[1]],pc[[1]],pd[[1]]]/.subQuart)//.{
					Quart[q_]:>((ListQuartic[[q,1]] ListQuartic[[q,7]][pa[[2]], pb[[2]], pc[[2]], pd[[2]]])(Times@@(Function[{x},ListQuartic[[q,6,x]][pa[[2+x]], pb[[2+x]], pc[[2+x]], pd[[2+x]]]]/@Range[NumberOfSubgroups])))}
				]
			];
		];
		
		BetaQuartic[pa_, pb_, pc_, pd_, la_, lb_, lc_, ld_, 1] := Module[
			{beta, ss, ii, x, ii2},
			beta = 0;
			beta = beta + Sqr[24]/8 Perm[\[CapitalLambda][Join[{pa}, la], Join[{pb}, lb], Join[{pc}, lc], Join[{pd}, ld]]]//.subQuartInv;
			beta = beta - Perm[H[Join[{pa}, la], Join[{pb}, lb], Join[{pc}, lc], Join[{pd}, ld]]]//.subQuartInv//.{tr[adj[a_], b_, adj[c_], d_]->tr[b, adj[c], d, adj[a]]};
			beta = beta + 24 \[CapitalLambda]Y[Join[{pa}, la], Join[{pb}, lb], Join[{pc}, lc], Join[{pd}, ld]]//.subQuartInv//.{tr[adj[a_], b_]->tr[b, adj[a]]};
			beta = beta - 3*24 Sum[Sqr[ListGauge[[ii,1]]]\[CapitalLambda]S[ii][Join[{pa}, la], Join[{pb}, lb], Join[{pc}, lc], Join[{pd}, ld]], {ii, 1, NumberOfSubgroups}]//.subQuartInv;
			beta = beta + 3/4 Sum[Sqr[ListGauge[[ii,1]]] Sqr[ListGauge[[ii2,1]]] Perm[As[ii,ii2][Join[{pa}, la], Join[{pb}, lb], Join[{pc}, lc], Join[{pd}, ld]]], {ii, 1, NumberOfSubgroups}, {ii2, 1, NumberOfSubgroups}]//.subQuartInv;
			Return[beta/(24 Sqr[4\[Pi]])];
		]
		
		
		
		(* Definition of Invariants *)
		ComputeInvariants[] := Module[
			{i, f, s},
			subInvariants = {};
			For[i=1, i<=NumberOfSubgroups, i++,
				(* Gauge Boson Invariants *)
				If[ListGauge[[i,2]] === U && ListGauge[[i,3]] === 1 && ListGauge[[i,4,i]] === 0,
					(* Singulet U(1) *)
					subInvariants = Append[subInvariants, d[ListGauge[[i,1]]]->1];
					subInvariants = Append[subInvariants, C2[ListGauge[[i,1]]]->0];,
					(* not U(1) *)
					If[ListGauge[[i,4,i]] === 1,
						(* gauge singulet: *)
						subInvariants = Append[subInvariants, C2[ListGauge[[i]]]->0];,
						(* no singulet: *)
						(* Adjoint Rep in SU(N)*)
						If[ListGauge[[i,2]] === SU && ListGauge[[i,4,i]]==Sqr[ListGauge[[i,3]]]-1,
							subInvariants = Append[subInvariants, d[ListGauge[[i,1]]]->ListGauge[[i,4,i]]];
							subInvariants = Append[subInvariants, C2[ListGauge[[i,1]]]->ListGauge[[i,3]]];
						];
					];
				];
				(* Fermion Invariants *)
				If[WeylFermionList != {},
					For[f=1, f<=FNumber[], f++,
						(* SU(N) subgroup *)
						If[ListGauge[[i,2]] === SU,
							If[WeylFermionList[[f,3,i]] === 1,
								subInvariants = Append[subInvariants, C2[WeylFermionList[[f,1]], ListGauge[[i,1]]]-> 0];
								subInvariants = Append[subInvariants, S2[WeylFermionList[[f,1]], ListGauge[[i,1]]]-> 0];
								Continue[];,
								(* Fundamental Representation *)
								If[WeylFermionList[[f,3,i]] == ListGauge[[i,3]],
									subInvariants = Append[subInvariants, C2[WeylFermionList[[f,1]], ListGauge[[i,1]]]-> 1/2 (Sqr[WeylFermionList[[f,3,i]]]-1)/WeylFermionList[[f,3,i]]];
									subInvariants = Append[subInvariants, S2[WeylFermionList[[f,1]], ListGauge[[i,1]]]-> 1/2 FMultiplicity[f]/WeylFermionList[[f,3,i]]];
								];
								(* Adjoint Representation *)
								If[WeylFermionList[[f,3,i]] == Sqr[ListGauge[[i,3]]] - 1,
									subInvariants = Append[subInvariants, C2[WeylFermionList[[f,1]], ListGauge[[i,1]]]-> ListGauge[[i,3]]];
									subInvariants = Append[subInvariants, S2[WeylFermionList[[f,1]], ListGauge[[i,1]]]-> FMultiplicity[f]/WeylFermionList[[f,3,i]] ListGauge[[i,3]]];
								];
							];
						];
						(* U(1) subgroup *)
						If[ListGauge[[i,2]] === U && ListGauge[[i,3]] === 1,
							subInvariants = Append[subInvariants, C2[WeylFermionList[[f,1]], ListGauge[[i,1]]]->Sqr[WeylFermionList[[f,3,i]]]];
							subInvariants = Append[subInvariants, S2[WeylFermionList[[f,1]], ListGauge[[i,1]]]->Sqr[WeylFermionList[[f,3,i]]] FMultiplicity[f]];
						];
					];
				];
				(* Scalar Invariants *)
				If[RealScalarList != {},
					For[s=1, s<=SNumber[], s++,
						(* SU(N) subgroup *)
						If[ListGauge[[i,2]] === SU,
							If[RealScalarList[[s,3,i]] === 1,
								subInvariants = Append[subInvariants, C2[RealScalarList[[s,1]], ListGauge[[i,1]]]-> 0];
								subInvariants = Append[subInvariants, S2[RealScalarList[[s,1]], ListGauge[[i,1]]]-> 0];
								subInvariants = Append[subInvariants, \[CapitalLambda][ListGauge[[i,1]], RealScalarList[[s,1]]][a_, b_, c_, d_]:>0];
								Continue[];,
								(* Fundamental Representation *)
								If[RealScalarList[[s,3,i]] == ListGauge[[i,3]],
									subInvariants = Append[subInvariants, C2[RealScalarList[[s,1]], ListGauge[[i,1]]]-> 1/2 (Sqr[RealScalarList[[s,3,i]]]-1)/RealScalarList[[s,3,i]]];
									subInvariants = Append[subInvariants, S2[RealScalarList[[s,1]], ListGauge[[i,1]]]-> 1/2 SMultiplicity[s]/RealScalarList[[s,3,i]]];
								];
								(* Adjoint Representation *)
								If[RealScalarList[[s,3,i]] == Sqr[ListGauge[[i,3]]] - 1,
									subInvariants = Append[subInvariants, C2[RealScalarList[[s,1]], ListGauge[[i,1]]]-> ListGauge[[i,3]]];
									subInvariants = Append[subInvariants, S2[RealScalarList[[s,1]], ListGauge[[i,1]]]-> SMultiplicity[s]/RealScalarList[[s,3,i]] ListGauge[[i,3]]];
								];
							];
						];
						(* U(1) subgroup *)
						If[ListGauge[[i,2]] === U && ListGauge[[i,3]] === 1,
							subInvariants = Append[subInvariants, C2[RealScalarList[[s,1]], ListGauge[[i,1]]]->Sqr[RealScalarList[[s,3,i]]]];
							subInvariants = Append[subInvariants, S2[RealScalarList[[s,1]], ListGauge[[i,1]]]->Sqr[RealScalarList[[s,3,i]]] SMultiplicity[s]];
						];
					];
				];
				(* Gauge-Yukawa Invariants *)
				If[WeylFermionList != {} && ListYukawa != {} && RealScalarList != {},
					subInvariants = Append[subInvariants, Y4[F, ListGauge[[i,1]]]-> (1/d[ListGauge[[i,1]]] Sum[ (YukawaTrace[C2[F, i], Yuk[ss], adj[Yuk[ss]], Table[KroneckerDelta[#2, #3]&, {ii, NumberOfSubgroups+1}]]) , {ss, 1, SNumber[]}])/.tr[a___, C2[b___], c___]->(C2[b] tr[a,c])//.{tr[adj[a_],b_]->tr[b,adj[a]], tr[adj[a_],b_,adj[c_],d_]->tr[b,adj[c],d,adj[a]]}];,
					subInvariants = Append[subInvariants, Y4[F, ListGauge[[i,1]]]->0];
				];
			];
		];
		
		(* Kronecker delta for arbitray list of arguments*)
		TensorDelta[{},{}] := 1;
		TensorDelta[a_List, b_List] := KroneckerDelta[a[[1]], b[[1]]] TensorDelta[Delete[a,1], Delete[b,1]];
		
		(* Matrix multiplication and traces for Yukawas *)
		subProd = {
			prod[a___, b_ + c_, d___]->prod[a, b, d] + prod[a, c, d],
			prod[a_]->a, 
			prod[a___, prod[b___], c___]->prod[a, b, c], 
			prod[a___, n_, b___]:>n prod[a,b] /; NumberQ[n],
			prod[a___, n_ c_, b___]:>n prod[a,c,b] /; NumberQ[n],
			prod[a___, 0, b___]->0,
			tr[a___, b_ + c_, d___]->tr[a, b, d] + tr[a, c, d],
			tr[a___, n_, b___]:>n tr[a,b] /; NumberQ[n], 
			tr[a___, n_ c_, b___]:>n tr[a,c,b] /; NumberQ[n], 
			tr[a___, 0, b___]->0,
			tr[a___, prod[b___], c___]->tr[a,b,c],
			adj[tr[a___]]->tr[adj[a]],
			adj[prod[a___]]->prod[adj[a]],
			prod[adj[a___,b___]]->prod[adj[b],adj[a]],
			tr[adj[a___,b___]]->tr[adj[b],adj[a]],
			adj[n_ a_]:> Conjugate[n] adj[a] /; NumberQ[n],
			prod[a___, tr[b___], c___]->tr[b] prod[a,c],
			tr[a___ prod[b___]]->a tr[b],
			adj[a_][i1_, i2_]->adj[a[i2, i1]],
			adj[adj[a_]]->a,
			adj[a_+ b_] -> adj[a] + adj[b],
			adj[0]->0
		};
		
		(* replaces Yukawas and other Invariants in Fermion traces and products *)
		subYuk = {
			Yuk[a_][i1_, i2_]:>
				Block[
					{posY, posYadj},
					posY = {};
					posYadj = {};
					If[ListYukawa != {},
						For[yuk = 1, yuk <= Dimensions[ListYukawa][[1]], yuk++,
							If[
								ListYukawa[[yuk,2]] == a && ListYukawa[[yuk,3]] == i1 && ListYukawa[[yuk,4]] == i2, 
								posY = Append[posY, yuk];
							];
						];
					];
					If[ListYukawa != {},
						For[yuk = 1, yuk <= Dimensions[ListYukawa][[1]], yuk++,
							If[
								ListYukawa[[yuk,2]] == a && ListYukawa[[yuk,3]] == i2 && ListYukawa[[yuk,4]] == i1, 
								posYadj = Append[posYadj, yuk];
							];
						];
					];
					If[posY != {}, Plus@@(Function[{x}, Hold[Yukawa[x]]]/@posY), 0] +  If[posYadj != {}, Plus@@(Function[{x}, adj[Hold[Yukawa[x]]]]/@posYadj), 0]
				],
				
			adj[Yukawa[pos_]]:>Join[
				{{adj[ListYukawa[[pos,1]]]//.subProd, Refine[Conjugate[ListYukawa[[pos,6]][#1,#3,#2]]]&, RealScalarList[[ListYukawa[[pos, 2]], 2]], WeylFermionList[[ListYukawa[[pos, 4]], 2]], WeylFermionList[[ListYukawa[[pos, 3]], 2]]}},
				Function[
					{x},
					Join[
						{(Refine[Conjugate[ListYukawa[[pos, 5, x]][#1,#3,#2]]])&}, 
						If[
							ListGauge[[x, 3]] === 1, 
							{1, 1, 1}, 
							{RealScalarList[[ListYukawa[[pos, 2]], 3, x]], WeylFermionList[[ListYukawa[[pos, 4]], 3, x]], WeylFermionList[[ListYukawa[[pos, 3]], 3, x]]}
						]
					]
				]/@Range[NumberOfSubgroups]
			],
			
			Yukawa[pos_]:>Join[
				{{ListYukawa[[pos,1]]//.subProd, ListYukawa[[pos,6]], RealScalarList[[ListYukawa[[pos, 2]], 2]], WeylFermionList[[ListYukawa[[pos, 3]], 2]], WeylFermionList[[ListYukawa[[pos, 4]], 2]]}},
				Function[
					{x},
					Join[
						{ListYukawa[[pos, 5, x]]}, 
						If[
							ListGauge[[x, 3]] === 1, 
							{1, 1, 1}, 
							{RealScalarList[[ListYukawa[[pos, 2]], 3, x]], WeylFermionList[[ListYukawa[[pos, 3]], 3, x]], WeylFermionList[[ListYukawa[[pos, 4]], 3, x]]}
						]
					]
				]/@Range[NumberOfSubgroups]
			],
			
			C2[F, igauge_][i1_, i2_] -> If[i1 == i2, C2F[i1, igauge], 0],
			C2F[ferm_, igauge_] :> Join[
				{{C2[WeylFermionList[[ferm, 1]], ListGauge[[igauge, 1]]],KroneckerDelta[#2,#3]&, 1, WeylFermionList[[ferm,2]], WeylFermionList[[ferm,2]]}},
				Function[{x}, If[ListGauge[[x, 3]] === 1, {1&, 1, 1, 1}, {KroneckerDelta[#2, #3]&, 1, WeylFermionList[[ferm, 3, x]], WeylFermionList[[ferm, 3, x]]}]]/@Range[NumberOfSubgroups]
			]
			
		};
		
		(* substitution rule for scalar sector *)
		subQuart := {
			Quartic[a_, b_, c_, d_] :> Block[
				{pos, qq},
				pos = {};
				If[ListQuartic != {},
					For[qq=1, qq<=Dimensions[ListQuartic][[1]], qq++,
						If[ListQuartic[[qq,2]] == a && ListQuartic[[qq,3]] == b && ListQuartic[[qq, 4]] == c && ListQuartic[[qq,5]] == d,
							pos = Append[pos, qq];
						];
					];
				];
				If[pos == {}, 
					0,
					Plus@@(Hold/@(Quart/@pos))
				]
			],
			Quart[q_] :> Join[
				{{ListQuartic[[q,1]], ListQuartic[[q,7]], RealScalarList[[ListQuartic[[q,2]], 2]], RealScalarList[[ListQuartic[[q,3]], 2]], RealScalarList[[ListQuartic[[q,4]], 2]], RealScalarList[[ListQuartic[[q,5]], 2]]}}, 
				Function[{x}, If[ListGauge[[x,3]] === 1, {ListQuartic[[q,6,x]], 1, 1, 1, 1}, {ListQuartic[[q,6,x]], RealScalarList[[ListQuartic[[q,2]], 3, x]], RealScalarList[[ListQuartic[[q,3]], 3, x]], RealScalarList[[ListQuartic[[q,4]], 3, x]], RealScalarList[[ListQuartic[[q,5]], 3, x]]}]]/@Range[NumberOfSubgroups]
			]
		};
		
		subQuartInv := {
			\[CapitalLambda][pa_, pb_, pc_, pd_] :> Block[
				{sum, i1, i2, s1, s2, perm1, perm2},
				sum=0;
				For[s1[0]=0, s1[0]<=SNumber[], s1[0]++,
					For[s2[0]=0, s2[0]<=SNumber[], s2[0]++,
						perm1 = Permutations[{pa, pb, Function[{x}, s1[x]]/@Range[0,NumberOfSubgroups+1], Function[{x}, s2[x]]/@Range[0,NumberOfSubgroups+1]}];
						perm2 = Permutations[{Function[{x}, s1[x]]/@Range[0,NumberOfSubgroups+1], Function[{x}, s2[x]]/@Range[0,NumberOfSubgroups+1], pc, pd}];
						For[i1=1, i1<=Dimensions[perm1][[1]], i1++,
							For[i2=1, i2<=Dimensions[perm1][[1]], i2++,
								sum = sum + (
									ReleaseHold[
										prod[
											Quartic[perm1[[i1, 1]][[1]], perm1[[i1, 2]][[1]], perm1[[i1, 3]][[1]], perm1[[i1, 4]][[1]]], 
											Quartic[perm2[[i2, 1]][[1]], perm2[[i2, 2]][[1]], perm2[[i2, 3]][[1]], perm2[[i2, 4]][[1]]]
										]//.subProd/.subQuart//.subProd]//.subQuart/.{prod[A_List, B_List]:>(SolveSProd2[A, B, Function[{x},
											((KroneckerDelta[perm1[[i1,1]][[1+x]],#1] KroneckerDelta[perm1[[i1,2]][[1+x]],#2] KroneckerDelta[perm1[[i1,3]][[1+x]],#3] KroneckerDelta[perm1[[i1,4]][[1+x]],#4] KroneckerDelta[perm2[[i2,1]][[1+x]],#5] KroneckerDelta[perm2[[i2,2]][[1+x]],#6] KroneckerDelta[perm2[[i2,3]][[1+x]],#7] KroneckerDelta[perm2[[i2,4]][[1+x]],#8])//.{KroneckerDelta[s1[x], aa_] KroneckerDelta[s1[x], bb_] :> KroneckerDelta[aa,bb], KroneckerDelta[s2[x], aa_] KroneckerDelta[s2[x], bb_] :> KroneckerDelta[aa,bb], Power[KroneckerDelta[s1[x], aa_],2] :> KroneckerDelta[aa,aa], Power[KroneckerDelta[s2[x], aa_],2] :> KroneckerDelta[aa,aa]})&
									]/@Range[NumberOfSubgroups+1]])}
								)/(Dimensions[perm1][[1]] Dimensions[perm2][[1]])
							];
						];
					];
				];
				sum
			],
			H[pa_, pb_, pc_, pd_] :> YukawaTrace[Yuk[pa[[1]]], adj[Yuk[pb[[1]]]], Yuk[pc[[1]]], adj[Yuk[pd[[1]]]], Function[
				{x},
				(KroneckerDelta[#1,pa[[1+x]]] KroneckerDelta[#2,pb[[1+x]]] KroneckerDelta[#3,pc[[1+x]]] KroneckerDelta[#4,pd[[1+x]]])&
			]/@Range[NumberOfSubgroups+1]],
			\[CapitalLambda]Y[pa_, pb_, pc_, pd_] :> ReleaseHold[(ReleaseHold[(Quartic[pa[[1]],pb[[1]],pc[[1]],pd[[1]]]/.subQuart)//.{
					Quart[q_]:>((ListQuartic[[q,1]] ListQuartic[[q,7]][pa[[2]], pb[[2]], pc[[2]], pd[[2]]])(Times@@(Function[{x},ListQuartic[[q,6,x]][pa[[2+x]], pb[[2+x]], pc[[2+x]], pd[[2+x]]]]/@Range[NumberOfSubgroups])))
				}]) Hold[
					Sum[
						YukawaTrace[Yuk[scal], adj[Yuk[scal]], Table[KroneckerDelta[#1, #2]&, {ii, NumberOfSubgroups+1}]],
						{scal, 1, SNumber[]}
					]
				]],
			\[CapitalLambda]S[gaug_][pa_, pb_, pc_, pd_] :> ReleaseHold[(ReleaseHold[(Quartic[pa[[1]],pb[[1]],pc[[1]],pd[[1]]]/.subQuart)//.{
					Quart[q_]:>((ListQuartic[[q,1]] ListQuartic[[q,7]][pa[[2]], pb[[2]], pc[[2]], pd[[2]]])(Times@@(Function[{x},ListQuartic[[q,6,x]][pa[[2+x]], pb[[2+x]], pc[[2+x]], pd[[2+x]]]]/@Range[NumberOfSubgroups])))
				}]) Hold[
					Sum[
						C2[RealScalarList[[scal,1]], ListGauge[[gaug,1]]] SMultiplicity[scal],
						{scal, 1, SNumber[]}
					]
				]],
			As[gaug1_, gaug2_][pa_, pb_, pc_, pd_] :> (
				A[gaug1, gaug2][pa, pb, pc, pd]
			)
		};

		(* sum over all fermions / scalars *)
		FSum[a___] := ReleaseHold[If[WeylFermionList == {}, 0, Sum[(a)&[sumindex], {sumindex,1,FNumber[]}]]];
		SSum[a___] := ReleaseHold[If[RealScalarList == {}, 0, Sum[(a)&[sumindex], {sumindex,1,SNumber[]}]]];

		
		(* overall multiplicity of particle *)
		FMultiplicity[f_] := WeylFermionList[[f,2]] Times@@(Function[{x},If[ListGauge[[x,3]]===1, 1, WeylFermionList[[f,3,x]]]]/@Range[NumberOfSubgroups]);
		SMultiplicity[s_] := RealScalarList[[s,2]] Times@@(Function[{x},If[ListGauge[[x,3]]===1, 1, RealScalarList[[s,3,x]]]]/@Range[NumberOfSubgroups]); 
		
		(* Yukawa trace and products of gauge indices *)
		SolveTrace2[y1_, y2_, ScGauge_] := Join[
			{ (tr[y1[[1,1]], y2[[1,1]]]//.subProd) 
				Refine[Sum[ScGauge[[1]][scGenIdx1, scGenIdx2] y1[[1,2]][scGenIdx1,sumInd1[0],sumInd2[0]] y2[[1,2]][scGenIdx2,sumInd2[0],sumInd1[0]],
					{sumInd1[0], 1, y1[[1,4]]}, 
					{sumInd2[0], 1, y1[[1,5]]},
					{scGenIdx1, 1, y1[[1,3]]},
					{scGenIdx2, 1, y2[[1,3]]}
				]]
			},
			((Function[{x}, Refine[Sum[
				ScGauge[[x+1]][scGaugeIdx1, scGaugeIdx2] y1[[x + 1, 1]][scGaugeIdx1, sumInd1[x], sumInd2[x]] y2[[x + 1, 1]][scGaugeIdx2, sumInd2[x], sumInd1[x]], 
				{sumInd1[x], 1, y1[[x+1, 3]]},
				{sumInd2[x], 1, y1[[x+1, 4]]},
				{scGaugeIdx1, 1, y1[[x+1, 2]]},
				{scGaugeIdx2, 1, y2[[x+1, 2]]}
			]]]) /@ Range[NumberOfSubgroups])
		];
		
		SolveTrace3[y1_, y2_, y3_,  ScGauge_] := Join[
			{ (tr[y1[[1,1]], y2[[1,1]], y3[[1,1]]]//.subProd) 
				Refine[Sum[
					ScGauge[[1]][scGenIdx1, scGenIdx2, scGenIdx3] y1[[1,2]][scGenIdx1,sumInd1[0],sumInd2[0]] y2[[1,2]][scGenIdx2,sumInd2[0],sumInd3[0]] y3[[1,2]][scGenIdx3,sumInd3[0],sumInd1[0]],
					{sumInd1[0], 1, y1[[1,4]]}, 
					{sumInd2[0], 1, y1[[1,5]]},
					{sumInd3[0], 1, y3[[1,4]]},
					{scGenIdx1, 1, y1[[1,3]]},
					{scGenIdx2, 1, y2[[1,3]]},
					{scGenIdx3, 1, y3[[1,3]]}
				]]
			},
			((Function[{x}, Refine[
				Sum[ScGauge[[x+1]][scGaugeIdx1, scGaugeIdx2, scGaugeIdx3] y1[[x+1, 1]][scGaugeIdx1, sumInd1[x], sumInd2[x]] y2[[x+1, 1]][scGaugeIdx2, sumInd2[x], sumInd3[x]]  y3[[x+1, 1]][scGaugeIdx3, sumInd3[x], sumInd1[x]], 
					{sumInd1[x], 1, y1[[x+1, 3]]}, 
					{sumInd2[x], 1, y1[[x+1, 4]]},
					{sumInd3[x], 1, y3[[x+1, 3]]},
					{scGaugeIdx1, 1, y1[[x+1, 2]]},
					{scGaugeIdx2, 1, y2[[x+1, 2]]},
					{scGaugeIdx3, 1, y3[[x+1, 2]]}
				]
			]]) /@ Range[NumberOfSubgroups])
		];
		
		SolveTrace4[y1_, y2_, y3_, y4_, ScGauge_] := Join[
			{ (tr[y1[[1,1]], y2[[1,1]], y3[[1,1]], y4[[1,1]]]//.subProd) 
				Refine[Sum[
					ScGauge[[1]][scGenIdx1, scGenIdx2, scGenIdx3, scGenIdx4] y1[[1,2]][scGenIdx1,sumInd1[0],sumInd2[0]] y2[[1,2]][scGenIdx2,sumInd2[0],sumInd3[0]] y3[[1,2]][scGenIdx3,sumInd3[0],sumInd4[0]] y4[[1,2]][scGenIdx4,sumInd4[0],sumInd1[0]],
					{sumInd1[0], 1, y1[[1,4]]}, 
					{sumInd2[0], 1, y1[[1,5]]},
					{sumInd3[0], 1, y3[[1,4]]},
					{sumInd4[0], 1, y3[[1,5]]},
					{scGenIdx1, 1, y1[[1,3]]},
					{scGenIdx2, 1, y2[[1,3]]},
					{scGenIdx3, 1, y3[[1,3]]},
					{scGenIdx4, 1, y4[[1,3]]}
				]]
			},
			((Function[{x}, Refine[
				Sum[ScGauge[[x+1]][scGaugeIdx1, scGaugeIdx2, scGaugeIdx3, scGaugeIdx4] y1[[x+1, 1]][scGaugeIdx1, sumInd1[x], sumInd2[x]] y2[[x+1, 1]][scGaugeIdx2, sumInd2[x], sumInd3[x]] y3[[x+1, 1]][scGaugeIdx3, sumInd3[x], sumInd4[x]] y4[[x+1, 1]][scGaugeIdx4, sumInd4[x], sumInd1[x]], 
					{sumInd1[x], 1, y1[[x+1, 3]]}, 
					{sumInd2[x], 1, y1[[x+1, 4]]},
					{sumInd3[x], 1, y3[[x+1, 3]]},
					{sumInd4[x], 1, y3[[x+1, 4]]},
					{scGaugeIdx1, 1, y1[[x+1, 2]]},
					{scGaugeIdx2, 1, y2[[x+1, 2]]},
					{scGaugeIdx3, 1, y3[[x+1, 2]]},
					{scGaugeIdx4, 1, y4[[x+1, 2]]}
				]
			]]) /@ Range[NumberOfSubgroups])
		];
		
		SolveProd1[y1_, pi_, pj_, Ll_, Lr_, ScGauge_] := Join[
			{ (prod[y1[[1,1]]][Ll[[1]],Lr[[1]]]//.subProd)
				Refine[Sum[
					ScGauge[[1]][scGenIdx1] y1[[1,2]][scGenIdx1, Ll[[1]], Lr[[1]]],
					{scGenIdx1, 1, y1[[1,3]]}
				]]
			},
			(Function[{x},Refine[Sum[
				ScGauge[[x+1]][scGaugeIdx1] y1[[x+1, 1]][scGaugeIdx1, Ll[[x+1]], Lr[[x+1]]],
				{scGaugeIdx1, 1, y1[[x+1, 2]]}
			]]]/@Range[NumberOfSubgroups])
		];
		
		SolveProd2[y1_, y2_, Ll_, Lr_, ScGauge_] := Join[
			{ (prod[y1[[1,1]],y2[[1,1]]][Ll[[1]],Lr[[1]]]//.subProd)
				Refine[Sum[
					ScGauge[[1]][scGenIdx1,scGenIdx2] y1[[1,2]][scGenIdx1, Ll[[1]], sumInd1[0]] y2[[1,2]][scGenIdx2, sumInd1[0], Lr[[1]]],
					{sumInd1[0], 1, y1[[1,5]]},
					{scGenIdx1, 1, y1[[1,3]]},
					{scGenIdx2, 1, y2[[1,3]]}
				]]
			},
			(Function[{x},Refine[Sum[
				ScGauge[[x+1]][scGaugeIdx1, scGaugeIdx2] y1[[x+1, 1]][scGaugeIdx1, Ll[[x+1]], sumInd1[x]] y2[[x+1, 1]][scGaugeIdx2, sumInd1[x], Lr[[x+1]]],
				{sumInd1[x], 1, y2[[x+1, 3]]},
				{scGaugeIdx1, 1, y1[[x+1, 2]]},
				{scGaugeIdx2, 1, y2[[x+1, 2]]}
			]]]/@Range[NumberOfSubgroups])
		];
		
		SolveProd3[y1_, y2_, y3_, Ll_, Lr_, ScGauge_] := Join[
			{ (prod[y1[[1,1]],y2[[1,1]],y3[[1,1]]][Ll[[1]],Lr[[1]]]//.subProd)
				Refine[Sum[
					ScGauge[[1]][scGenIdx1,scGenIdx2,scGenIdx3] y1[[1,2]][scGenIdx1, Ll[[1]], sumInd1[0]] y2[[1,2]][scGenIdx2, sumInd1[0], sumInd2[0]] y3[[1,2]][scGenIdx3, sumInd2[0], Lr[[1]]],
					{sumInd1[0], 1, y1[[1,5]]},
					{sumInd2[0], 1, y2[[1,4]]},
					{scGenIdx1, 1, y1[[1,3]]},
					{scGenIdx2, 1, y2[[1,3]]},
					{scGenIdx3, 1, y3[[1,3]]}
				]]
			},
			(Function[{x},Refine[Sum[
				ScGauge[[x+1]][scGaugeIdx1, scGaugeIdx2, scGaugeIdx3] y1[[x+1, 1]][scGaugeIdx1, Ll[[x+1]], sumInd1[x]] y2[[x+1, 1]][scGaugeIdx2, sumInd1[x],sumInd2[x]] y3[[x+1, 1]][scGaugeIdx3, sumInd2[x],Lr[[x+1]]],
				{sumInd1[x], 1, y2[[x+1, 3]]},
				{sumInd2[x], 1, y2[[x+1, 4]]},
				{scGaugeIdx1, 1, y1[[x+1, 2]]},
				{scGaugeIdx2, 1, y2[[x+1, 2]]},
				{scGaugeIdx3, 1, y3[[x+1, 2]]}
			]]]/@Range[NumberOfSubgroups])
		];
		
		SolveProd4[y1_, y2_, y3_, y4_, Ll_, Lr_, ScGauge_] := Join[
			{ (prod[y1[[1,1]],y2[[1,1]],y3[[1,1]],y4[[1,1]]][Ll[[1]],Lr[[1]]]//.subProd)
				Refine[Sum[
					ScGauge[[1]][scGenIdx1,scGenIdx2,scGenIdx3,scGenIdx4] y1[[1,2]][scGenIdx1, Ll[[1]], sumInd1[0]] y2[[1,2]][scGenIdx2, sumInd1[0], sumInd2[0]] y3[[1,2]][scGenIdx3, sumInd2[0], sumInd3[0]] y4[[1,2]][scGenIdx4, sumInd3[0], Lr[[1]]],
					{sumInd1[0], 1, y1[[1,5]]},
					{sumInd2[0], 1, y2[[1,4]]},
					{sumInd3[0], 1, y2[[1,5]]},
					{scGenIdx1, 1, y1[[1,3]]},
					{scGenIdx2, 1, y2[[1,3]]},
					{scGenIdx3, 1, y3[[1,3]]},
					{scGenIdx4, 1, y4[[1,3]]}
				]]
			},
			(Function[{x},Refine[Sum[
				ScGauge[[x+1]][scGaugeIdx1, scGaugeIdx2, scGaugeIdx3, scGaugeIdx4] y1[[x+1, 1]][scGaugeIdx1, Ll[[x+1]], sumInd1[x]] y2[[x+1, 1]][scGaugeIdx2, sumInd1[x],sumInd2[x]] y3[[x+1, 1]][scGaugeIdx3,sumInd2[x],sumInd3[x]] y4[[x+1, 1]][scGaugeIdx4, sumInd3[x], Lr[[x+1]]]
				{sumInd1[x], 1, y2[[x+1, 3]]},
				{sumInd2[x], 1, y2[[x+1, 4]]},
	 			{sumInd3[x], 1, y3[[x+1, 3]]},
				{scGaugeIdx1, 1, y1[[x+1, 2]]},
				{scGaugeIdx2, 1, y2[[x+1, 2]]},
				{scGaugeIdx3, 1, y3[[x+1, 2]]},
				{scGaugeIdx4, 1, y4[[x+1, 2]]}
			]]]/@Range[NumberOfSubgroups])
		];
		
		
		SolveProd5[y1_, y2_, y3_, y4_, y5_, Ll_, Lr_, ScGauge_] := Join[
			{ (prod[y1[[1,1]],y2[[1,1]],y3[[1,1]],y4[[1,1]],y5[[1,1]]][Ll[[1]],Lr[[1]]]//.subProd)
				Refine[Sum[
					ScGauge[[1]][scGenIdx1,scGenIdx2,scGenIdx3,scGenIdx4,scGenIdx5] y1[[1,2]][scGenIdx1, Ll[[1]], sumInd1[0]] y2[[1,2]][scGenIdx2, sumInd1[0], sumInd2[0]] y3[[1,2]][scGenIdx3, sumInd2[0], sumInd3[0]] y4[[1,2]][scGenIdx4, sumInd3[0], sumInd4[0]] y4[[1,2]][scGenIdx5, sumInd4[0], Lr[[1]]],
					{sumInd1[0], 1, y1[[1,5]]},
					{sumInd2[0], 1, y2[[1,4]]},
					{sumInd3[0], 1, y2[[1,5]]},
					{sumInd4[0], 1, y2[[1,5]]},
					{scGenIdx1, 1, y1[[1,3]]},
					{scGenIdx2, 1, y2[[1,3]]},
					{scGenIdx3, 1, y3[[1,3]]},
					{scGenIdx4, 1, y4[[1,3]]},
					{scGenIdx5, 1, y5[[1,3]]}
				]]
			},
			(Function[{x},Refine[Sum[
				ScGauge[[x+1]][scGaugeIdx1, scGaugeIdx2, scGaugeIdx3, scGaugeIdx4, scGaugeIdx5] y1[[x+1, 1]][scGaugeIdx1, Ll[[x+1]], sumInd1[x]] y2[[x+1, 1]][scGaugeIdx2, sumInd1[x],sumInd2[x]] y3[[x+1, 1]][scGaugeIdx3,sumInd2[x],sumInd3[x]] y4[[x+1, 1]][scGaugeIdx4, sumInd3[x], sumInd4[x]] y5[[x+1, 1]][scGaugeIdx5, sumInd4[x], Lr[[x+1]]],
				{sumInd1[x], 1, y2[[x+1, 3]]},
				{sumInd2[x], 1, y2[[x+1, 4]]},
	 			{sumInd3[x], 1, y3[[x+1, 3]]},
				{sumInd4[x], 1, y3[[x+1, 4]]},
				{scGaugeIdx1, 1, y1[[x+1, 2]]},
				{scGaugeIdx2, 1, y2[[x+1, 2]]},
				{scGaugeIdx3, 1, y3[[x+1, 2]]},
				{scGaugeIdx4, 1, y4[[x+1, 2]]},
				{scGaugeIdx5, 1, y5[[x+1, 2]]}
			]]]/@Range[NumberOfSubgroups])
		];
		
		(* traces and products of fermion type indices *)
		SolveProd[a_, b___, c_, i1_, i2_] := Sum[prod[
			a[i1, s1], SolveProd[b, s1, s2], c[s2, i2]],
			{s1, 1, FNumber[]}, {s2, 1, FNumber[]}
		];
		SolveProd[i1_, i2_] := KroneckerDelta[i1, i2];
		SolveProd[a_, i1_, i2_] := prod[a[i1,i2]];
		SolveTrace[a___] := Sum[tr[SolveProd[a, s, s]], {s, 1, FNumber[]}];
		
		(* combined traces over type and gauge indices for yukawa chains *)
		YukawaTrace[a___, SGauge_] := ReleaseHold[(ReleaseHold[SolveTrace[a] //.subProd /.subYuk //.subProd]//.subYuk //.{tr[y1_, y2_]->Hold[Times@@SolveTrace2[y1, y2, SGauge]], tr[y1_, y2_, y3_]->Hold[Times@@SolveTrace3[y1, y2, y3, SGauge]], tr[y1_, y2_, y3_, y4_]->Hold[Times@@SolveTrace4[y1, y2, y3, y4, SGauge]]})];
		YukawaProd[a___, pl_, pr_, LstL_, LstR_, SGauge_] := ReleaseHold[(ReleaseHold[SolveProd[a, pl, pr] //.subProd /.subYuk //.subProd]//.subYuk //.{tr[y1_, y2_]->Hold[Times@@SolveTrace2[y1, y2, SGauge]], tr[y1_, y2_, y3_]->Hold[Times@@SolveTrace3[y1, y2, y3, SGauge]], tr[y1_, y2_, y3_, y4_]->Hold[Times@@SolveTrace4[y1, y2, y3, y4, SGauge]], prod[y1_]->Hold[Times@@SolveProd1[y1, LstL, LstR, SGauge]], prod[y1_, y2_]->Hold[Times@@SolveProd2[y1, y2, LstL, LstR, SGauge]], prod[y1_, y2_, y3_]->Hold[Times@@SolveProd3[y1, y2, y3, LstL, LstR, SGauge]], prod[y1_, y2_, y3_, y4_]->Hold[Times@@SolveProd4[y1, y2, y3, y4, LstL, LstR, SGauge]], prod[y1_, y2_, y3_, y4_, y5_]->Hold[Times@@SolveProd5[y1, y2, y3, y4, y5, LstL, LstR, SGauge]]})];
		
		(* permutation *)
		Perm[f_[a_,b_,c_,d_]]:=(f[a,b,c,d] + f[a,b,d,c] + f[a,c,b,d] + f[a,c,d,b] + f[a,d,b,c] + f[a,d,c,b] + f[b,a,c,d] + f[b,a,d,c] + f[b,c,a,d] + f[b,c,d,a] + f[b,d,a,c] + f[b,d,c,a] + f[c,a,b,d] + f[c,a,d,b] + f[c,b,a,d] + f[c,b,d,a] + f[c,d,a,b] + f[c,d,b,a] + f[d,a,b,c] + f[d,a,c,b] + f[d,b,a,c] + f[d,b,c,a] + f[d,c,a,b] + f[d,c,b,a]); 
		
		(* scalar quartic products *)
		SolveSProd2[Q1_, Q2_, SContr_] := Times@@Join[
			{ (Q1[[1,1]] Q2[[1,1]])
				Sum[
					SContr[[1]][q1Idx1[0], q1Idx2[0], q1Idx3[0], q1Idx4[0], q2Idx1[0], q2Idx2[0], q2Idx3[0], q2Idx4[0]] Q1[[1,2]][q1Idx1[0], q1Idx2[0], q1Idx3[0], q1Idx4[0]] Q2[[1,2]][q2Idx1[0], q2Idx2[0], q2Idx3[0], q2Idx4[0]],
					{q1Idx1[0], 1, Q1[[1,3]]},
					{q1Idx2[0], 1, Q1[[1,4]]},
					{q1Idx3[0], 1, Q1[[1,5]]},
					{q1Idx4[0], 1, Q1[[1,6]]},
					{q2Idx1[0], 1, Q2[[1,3]]},
					{q2Idx2[0], 1, Q2[[1,4]]},
					{q2Idx3[0], 1, Q2[[1,5]]},
					{q2Idx4[0], 1, Q2[[1,6]]}
				]
			},
			(Function[{x},
				Sum[
					SContr[[1+x]][q1Idx1[x], q1Idx2[x], q1Idx3[x], q1Idx4[x], q2Idx1[x], q2Idx2[x], q2Idx3[x], q2Idx4[x]] Q1[[1+x,1]][q1Idx1[x], q1Idx2[x], q1Idx3[x], q1Idx4[x]] Q2[[1+x,1]][q2Idx1[x], q2Idx2[x], q2Idx3[x], q2Idx4[x]],
					{q1Idx1[x], 1, Q1[[1+x,2]]},
					{q1Idx2[x], 1, Q1[[1+x,3]]},
					{q1Idx3[x], 1, Q1[[1+x,4]]},
					{q1Idx4[x], 1, Q1[[1+x,5]]},
					{q2Idx1[x], 1, Q2[[1+x,2]]},
					{q2Idx2[x], 1, Q2[[1+x,3]]},
					{q2Idx3[x], 1, Q2[[1+x,4]]},
					{q2Idx4[x], 1, Q2[[1+x,5]]}
				]
			]/@Range[NumberOfSubgroups])
		];
		
		(* number of real scalars and weyl fermions *)
		SNumber[] := If[RealScalarList == {}, 0, Dimensions[RealScalarList][[1]]];
		FNumber[] := If[WeylFermionList == {}, 0, Dimensions[WeylFermionList][[1]]];
		
		(* Error Messages *)
		Gauge::RepMismatch = "Representation list does not match number of subgroups";
		WeylFermion::RepMismatch = "Representation list does not match number of subgroups";
		RealScalar::RepMismatch = "Representation list does not match number of subgroups";
		Yukawa::ContractionError = "Number of gauge contractions does not match number of subgroups";
		Yukawa::UnknownParticle = "Undefined particle in Yukawa sector";
		Quartic::ContractionError = "Number of gauge contractions does not match number of subgroups";
		Quartic::UnknownParticle = "Undefined particle in scalar sector";
		
		Reset[];
	(*End[];*)
EndPackage[];
