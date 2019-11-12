#load "Core.fsx"
open Core
open FsCheck

relation 
    (step 1.0 "1"
     ^= step 1.0 "2"
     ^< step 2.0 "3"
     ^< step 3.0 "4"
     ^< value 4.0)
|> Check.Quick

// All the proof steps in more readable form.
