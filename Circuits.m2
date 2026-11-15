-- Circuit and leading-term generation for K_(4,t).
-- Edge (i,j), 0 <= i < 4 and 0 <= j < t, has bit index t*i+j.
-- Lexicographic comparison of squarefree monomials therefore compares masks
-- from the highest indexed edge downwards, as in the accompanying certificate.

k4HasBit = (m,k) -> ((m // 2^k) % 2 == 1);
k4PopCount = m -> (
    ans := 0;
    while m > 0 do (ans = ans + m % 2; m = m // 2);
    ans
    );
k4MaskEdges = (m,t) -> select(toList(0..(4*t-1)), e -> k4HasBit(m,e));

-- Return the largest complementary spanning-tree mask.  Each search node
-- partitions a prefix of the edges into two forests.  The higher edge is
-- tried in the first forest before it is tried in the second.  A successful
-- partition of 2*n-2 edges into forests has n-1 edges in each forest, so both
-- are spanning trees on the circuit's active vertices.  The order of this
-- exhaustive, cycle-pruned search proves lexicographic maximality.
k4LeadingTree = (circuit,t) -> (
    edges := reverse k4MaskEdges(circuit,t);
    firstParent := new MutableList from toList(0..(t+3));
    secondParent := new MutableList from toList(0..(t+3));
    rootOf := (p,u) -> (while p#u != u do u = p#u; u);
    search := null;
    search = (pos,mask) -> (
        if pos == #edges then return mask;
        e := edges#pos;
        u := e // t;
        v := 4 + e % t;
        a := rootOf(firstParent,u);
        b := rootOf(firstParent,v);
        ans := -1;
        if a != b then (
            firstParent#b = a;
            ans = search(pos+1,mask+2^e);
            firstParent#b = b;
            );
        if ans != -1 then return ans;
        a = rootOf(secondParent,u);
        b = rootOf(secondParent,v);
        if a != b then (
            secondParent#b = a;
            ans = search(pos+1,mask);
            secondParent#b = b;
            );
        ans
        );
    ans := search(0,0);
    if ans == -1 then error "No complementary spanning-tree partition";
    ans
    );

-- Independent acyclicity check for a proposed tree, including its size.
k4IsTree = (mask,activeVertices,t) -> (
    if k4PopCount(mask) != #activeVertices-1 then return false;
    parent := new MutableList from toList(0..(t+3));
    rootOf := u -> (while parent#u != u do u = parent#u; u);
    good := true;
    scan(k4MaskEdges(mask,t),e -> (
        a := rootOf(e//t);
        b := rootOf(4+e%t);
        if a == b then good = false else parent#b = a;
        ));
    good
    );

-- The four circuit families in the proved K_(4,t) classification are:
-- K_(4,3), K_(3,4), K_(4,4) minus a matching of size two,
-- K_(4,5) minus four edges in distinct columns with row multiplicity <= 2,
-- K_(4,6) minus one edge per column with row multiplicity <= 3.
k4CircuitMasks = t -> (
    if t < 0 then error "t must be nonnegative";
    columns := if t == 0 then {} else toList(0..(t-1));
    circuitSet := new MutableHashTable;
    addCircuit := m -> (circuitSet#m = true;);
    rectangle := (rows,cols) -> sum(rows, i -> sum(cols, j -> 2^(t*i+j)));
    if t >= 3 then scan(subsets(columns,3), cols ->
        addCircuit rectangle(toList(0..3),cols));
    if t >= 4 then scan(subsets(columns,4), cols -> (
        scan(toList(0..3), omitted ->
            addCircuit rectangle(select(toList(0..3),i -> i != omitted),cols));
        full := rectangle(toList(0..3),cols);
        scan(subsets(cols,2), removedColumns ->
            scan(toList(0..3), i -> scan(toList(0..3), k -> (
                if i != k then addCircuit(full
                    - 2^(t*i+removedColumns#0)
                    - 2^(t*k+removedColumns#1));
                ))));
        ));
    assignments := (length,bound) -> select(
        apply(toList(0..(4^length-1)), q ->
            apply(toList(0..(length-1)),j -> (q // 4^j)%4)),
        word -> all(toList(0..3), i -> #select(word,j -> i == j) <= bound));
    if t >= 5 then (
        words4 := assignments(4,2);
        scan(subsets(columns,5), cols -> (
            full := rectangle(toList(0..3),cols);
            scan(subsets(cols,4), removedColumns -> scan(words4,word ->
                addCircuit(full-sum(toList(0..3),j ->
                    2^(t*word#j+removedColumns#j)))));
            ));
        );
    if t >= 6 then (
        words6 := assignments(6,3);
        scan(subsets(columns,6), cols -> (
            full := rectangle(toList(0..3),cols);
            scan(words6,word -> addCircuit(full-sum(toList(0..5),j ->
                2^(t*word#j+cols#j))));
            ));
        );
    sort keys circuitSet
    );

k4ExpectedCircuitCount = t -> (
    chooseSafe := (n,k) -> if n < k then 0 else binomial(n,k);
    chooseSafe(t,3)+76*chooseSafe(t,4)
        +1020*chooseSafe(t,5)+3480*chooseSafe(t,6)
    );

k4CircuitData = t -> (
    masks := k4CircuitMasks t;
    if #masks != k4ExpectedCircuitCount t then error "Circuit count mismatch";
    apply(masks,mask -> (
        leading := k4LeadingTree(mask,t);
        active := sort unique flatten apply(k4MaskEdges(mask,t),e -> {e//t,4+e%t});
        assert(k4PopCount(mask) == 2*#active-2);
        assert(k4IsTree(leading,active,t));
        assert(k4IsTree(mask-leading,active,t));
        {mask,leading}
        ))
    );
