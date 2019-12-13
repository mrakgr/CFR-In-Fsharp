let coreq e sum S u psi i j k = 
    sum S (fun s -> if s i <> j then 0.0 else psi s * (u i (fun i' -> if i = i' then k else s i') + u i s)) <= e