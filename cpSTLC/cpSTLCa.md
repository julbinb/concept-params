## Simply Typed Lambda Calculus with Concept Parameters: version a

STLC with `Nat` and `Bool` with simple **concept parameters**:

*   **Concepts** contains only names with types
    
    ```
    C := <empty>
       | CDef C
       
    CDef ::= concept Id 
               f1 : T1
               f2 : T2
               ...
               fn : Tn
             endc  
    ```
    
*   **Models** consist of concept-names definitions:

    ```
    M := <empty>
       | MDef M
       
    MDef ::= model Id of Id
               f1 = t1
               f2 = t2
               ...
               fn = tn
             endm
    ```
    
*   **Types** are STLC types with _concept parameters_:
    
    ```
    T ::= Nat
        | Bool
        | T -> T    (function)
        | C # T     (concept parameter, C is a concept)
    ```
    
*   **Terms** are STLC terms with _model applications_:

    ```
    t ::= true
        | false
        | n          (natural constant)
        | pred t
        | succ t
        | mult t t
        | if t then t else t
        | t t
        | \x:T.t
        | t # m      (model application)
        | \c#C.t     (c is a concept parameter of concept C)
    ```
