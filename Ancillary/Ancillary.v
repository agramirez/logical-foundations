Module SevenStepMethod.

Inductive condition : Type :=
    | New
    | Good
    | Worn
    | Damaged
    | Broken.

Inductive defect : Type :=
    | NoDefect
    | AirLoss (psi:nat)
    | AirExcess (psi:nat)
    | ThreadDepth (in32nd:nat)
    | FabricShow
    | Cut
    | ThreadSeparation
    | BadContact
    | SizeMismatch
    | TypeMismatch
    | Cracked
    | Rewored.

Inductive longitudinal : Type := | Front | Rear.
Inductive vertical : Type := | Top | Bottom. 
Inductive horizontal : Type := | Passenger | Driver.
Inductive order : Type := | First | Second | Third | Fourth | Fifth.

Inductive location : Type :=
    | Location (l:longitudinal) (s:horizontal) (v:vertical) .

Inductive part : Type := 
    | Part (l:location)
    | Tire (p:part) (o:order)
    | SteeringArm (p:part).

Inductive part_list : Type := | nil_part | cons_part (p:part) (l:part_list).

Inductive inspection : Type := 
    | Inspection (p:part) (c:condition) (d:defect).

Inductive inspection_list : Type :=
    | nil_inspect
    | cons_inspect (i:inspection) (l:inspection_list).

Inductive vehicle : Type :=
    | Truck (parts:part_list).

Inductive reporting : Type := | Pre | During | Post.

Inductive report : Type :=
    | Report (r:reporting) (v:vehicle) (il:inspection_list).

Definition tire1 := (Tire (Part (Location Front Driver Bottom)) First).
Definition tire2 := (Tire (Part (Location Rear Driver Bottom)) First).
Definition tire3 := (Tire (Part (Location Rear Passenger Bottom)) First).
Definition tire4 := (Tire (Part (Location Front Passenger Bottom)) First).

Check (Inspection tire1 Good NoDefect).
Check (Inspection tire2 Good NoDefect).
Check (Inspection tire3 Good NoDefect).
Check (Inspection tire4 Good NoDefect).

Definition steeringArm1 := (SteeringArm (Part (Location Front Driver Bottom))).
Definition steeringArm2 := (SteeringArm (Part (Location Front Passenger Bottom))).

Check (Inspection steeringArm1 Good NoDefect).
Check (Inspection steeringArm2 Good NoDefect).

End SevenStepMethod.