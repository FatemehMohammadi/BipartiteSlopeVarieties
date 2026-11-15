-- Independent  Macaulay2 checks for the determinantal models and
-- applications.  Load this file and
-- run runAlgebraChecks().  

algebraK3Check = (kk,t) -> (
    R := kk[Variables => 3*t];
    q := gens R;
    M := matrix apply(t,i -> {
        q#(3*i)-q#(3*i+1),
        q#(3*i)-q#(3*i+2),
        q#(3*i+2)*(q#(3*i)-q#(3*i+1)),
        q#(3*i+1)*(q#(3*i)-q#(3*i+2))});
    I := minors(4,M);
    A := coker gens I;
    C := res A;
    assert(dim A == 2*t+3);
    assert(length C == t-3);
    scan(toList(1..(t-3)),i -> (
        wanted := flatten apply(toList(0..(i-1)),j ->
            apply(binomial(t,i+3)*(i-j)*(j+1),k -> {i+5+j}));
        assert(sort degrees C_i == sort wanted);
        ));
    assert(regularity A == t+1);
    assert(degree A == t+2+(t-4)*2^(t-1));
    assert(rank C_(t-3) == binomial(t-1,3));
    hs := hilbertSeries(A,Reduce => true);
    h := numerator hs;
    z := first gens ring h;
    expected := (1+z)^(t-1)*(1-2*z+(t-3)*z^2)
        +3*z^2+(t-1)*z^3;
    assert(h == expected);
    print concatenate("PASS K_(3,",toString t,
        ") native resolution and Hilbert series over ",toString kk);
    true
    );

algebraScrollCheck = r -> (
    R := QQ[Variables => r+1];
    q := take(gens R,r);
    w := (gens R)#r;
    -- Fixed neighbours are P_j=(j,j^2), 0<=j<r.  Distinct first
    -- coordinates and noncollinearity suffice; balanced type is not assumed.
    M := matrix apply(toList(1..(r-1)),j ->
        {q#j-q#0,j^2*w-j*q#j});
    A := coker gens minors(2,M);
    C := res A;
    assert(dim A == 3);
    assert(degree A == r-1);
    assert(regularity A == 1);
    assert(length C == r-2);
    scan(toList(1..(r-2)),i -> (
        assert(degrees C_i == apply(i*binomial(r-1,i+1),j -> {i+1}));
        ));
    hs := hilbertSeries(A,Reduce => true);
    h := numerator hs;
    z := first gens ring h;
    assert(h == 1+(r-2)*z);
    print concatenate("PASS ",toString r,
        " fixed neighbours: scroll Eagon-Northcott resolution");
    true
    );

algebraApplicationsCheck = () -> (
    R := QQ[Variables => 12];
    q := gens R;
    M := matrix apply(4,j -> {
        q#j-q#(4+j), q#j-q#(8+j),
        q#(8+j)*(q#j-q#(4+j)),
        q#(4+j)*(q#j-q#(8+j))});
    tau := det M;
    assert(degree tau == {6});
    assert(#terms tau == 216);
    -- A rational planar drawing: all seven first coordinates are distinct.
    -- Slopes join hubs 0,1,2 to landmarks 3,4,5,6 in a common frame.
    points := apply(7,i -> {i,i^3+2*i^2-i});
    slope := (i,j) -> ((points#j)#1-(points#i)#1)/
                         ((points#j)#0-(points#i)#0);
    evalDrawing := map(QQ,R,flatten apply(3,i ->
        apply(4,j -> slope(i,3+j))));
    assert(evalDrawing tau == 0);
    -- Rooted Hodges/pentad projection: seven root coordinates followed
    -- by the twelve K_(3,4) coordinates.  Work in the fraction field only
    -- for the substitution; the cleared result must lift back to S.
    S := QQ[Variables => 19];
    v := gens S;
    a := take(v,7);
    z := drop(v,7);
    K := frac S;
    ratioMap := map(K,R,flatten apply(3,i ->
        apply(4,j -> z#(4*i+j)/(a#i*a#(3+j)))));
    clearing := product(take(a,3),u -> u^3)
        *product(drop(a,3),u -> u^2);
    F := lift(clearing*ratioMap(tau),S);
    assert(degree F == {11});
    assert(numgens S == 19);
    assert(#terms F == 216);
    assert(clearing*ratioMap(tau) == F);
    -- No root variable divides the cleared polynomial: the displayed
    -- clearing exponents are sharp, as required by the projective example.
    scan(toList(0..6),i -> assert(sub(F,v#i=>0) != 0));
    print "PASS applications: sextic bearing compatibility and degree-11 rooted pentad identity";
    true
    );

runAlgebraChecks = () -> (
    scan({QQ,ZZ/2,ZZ/3},kk -> scan({4,5,6},t -> algebraK3Check(kk,t)));
    scan({3,4,5},r -> algebraScrollCheck r);
    algebraApplicationsCheck();
    print "PASS all independent native Macaulay2 algebra checks";
    true
    );
