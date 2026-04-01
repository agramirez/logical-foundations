(******************************************************************************
Author:         Alexander G Ramirez
Description:    This module contains information pertinant to the Illinois CDL
                Study Guide.


******************************************************************************)
From Stdlib Require Import String.
Open Scope string_scope.

Module Section1.

Inductive section : Type :=
    | Section (title:string) (start:nat) (finish:nat).

Inductive abbreviation : Type :=
    | Abbreviation (value:string) (description:string).

Inductive fact : Type :=
    | Fact (key:string) (title:string) (definition:string).

Inductive vehicle : Type :=
    | none
    | Vehicle (gvwr:nat) (passengers:nat) (hazzard_transport:bool) (towed:vehicle).

Definition section_one := (Section "Introduction to Illinois CDL" 2 8).

Definition cmvsa := (Fact 
    "CMV Safety Act", 
    "Created date and purpose", 
    "In 1986 congress passed the Commercial Motor Vehicle Safety Act which sets 
    the minimum standards for licensing of drivers of Commercial Motor Vehicles 
    (CMV)"
).

Definition cdl := (Abbreviation 
    "CDL",
    "Commercial Driver's License"
).
Definition cmv := (Abbreviation
    "CMV",
    "Commercial Motor Vehicle"
).
Definition clp := (Abbreviation
    "CLP",
    "Commercial Driver's License Learner's Permit"
).
Definition fmcsa := (Abbreviation
    "FMCSA",
    "Federal Motor Carrier Safety Administration"
).
Definition sdla := (Abbreviation
    "SDLA)",
    "State Driver License Agencies"
).

Definition dach := (Fact
    "The Clearinghouse",
    "Dach Clearing House",
    "The Dach Clearing House gives real time access to current CDL and CLP 
    holder's drug and alcohol program violations to FMCSA, SDLAs, and state law
    enforcement personnel"
).

Definition gvwr := (Abbreviation
    "GVWR",
    "Gross Vehicle Weight Rating"
).

Definition gCvwr := (Abbreviation
    "GCVWR",
    "Gross Combined Vehicle Weight Rating"
).

Definition gCvwrDef := (Fact
    "GCVWR",
    "Gross Combined Vehicle Weight Rating",
    "Value specified by the manufacturer as the GVWR of the power unit plus the
    GVWR of the towed unit or units"
).

Definition andb (b1 b2:bool) : bool :=
    if b1 then b2 else false.

Definition orb (b1 b2:bool) : bool :=
    if b1 then true else b2.

Fixpoint gtb (m n:nat) : bool :=
    match m,n with
        |S m',O => true
        |S m', S n' => gtb m' n'
        |_,_ => false
    end.
Notation "x >? y" := (gtb x y)(at level 60).

Definition cdl_required 
    (gvwr gCvwr towed_gvwr passengers:nat) (hazzard_transport:bool) :=
    if (andb (gtb gCvwr 26_000) (gtb towed_gvwr 10_000)) then   
        true
    else if (orb (gtb gvwr 26_000) (gtb towed_gvwr 10_000)) then
        true
    else if (gtb passengers 14) then
        true
    else if hazzard_transport then
        true
    else
        false.

Example cdl_for_tractor: (cdl_required 26_000 26_000 0 1 false) = false.
Proof. simpl. reflexivity. Qed.

Example cdl_for_f250_with_max_load: (cdl_required 2600 12_600 10_000 6 false) = false.
Proof. simpl. reflexivity. Qed.

Example cdl_for_f250_with_overload: (cdl_required 2600 12_600 12_000 6 false) = true.
Proof. simpl. reflexivity. Qed.

Definition except_farm := (Fact
    "Except Farm",
    "Farm Workers Exception from CDL Requirements",
    "Farm equipment is excempt if it is
        — Controlled and operated by a farmer, the farmer’s family or an employee;
        — Used to transport farm products, equipment or supplies to or from a 
          farm (including nurseries and aquacultures);
        — Used within 150 air miles of the farm; and
        — Not used in the operations of a common or contract carrier or for other 
          commercial purposes."
).

Definition except_farm_classA := (Fact
    "Class A Farm Excempt",
    "Class A Drivers even if farm Excempt, still need CDL testing",
    "Note: Operators of Class A, truck-tractor and semi-trailer combination 
     vehicles used expressly for farming purposes and who meet the criteria for 
     farm exception are also exempted from holding a CDL. These drivers must 
     still possess a Class A non-CDL with a J50, J51, or J52 restriction. Drivers 
     must be of qualifying age and must be qualified as a Farm Vehicle Driver 
     (FVD) or the vehicle(s) must meet the Covered Farm Vehicle (CFV) designation. 
     Drivers are still required to take the appropriate CDL written and skills/drive 
     testing. For more information and definition, visit ilsos.gov, Commercial 
     section."
).

Definition except_emergency := (Fact 
    "Emergency Vehicle Excemption",
    "Drivers of emergency vehicles are excempt",
    "Emergency Equipment/Vehicle. Because most emergency organizations have 
    extensive initial training and retraining requirements for their equipment 
    operators, Illinois waives CDL requirements for operators of emergency 
    equipment vehicles when responding to or returning from an emergency necessary 
    to preserve life and property.").

Definition except_military := (Fact
    "Military Excemption",
    "Military Vehicles are Excempt",
    "Military Vehicle. Military vehicles operated by active duty military personnel."
).

Definition except_rv := (Fact 
    "RV Exception",
    "RVs are Excempt",
    "Recreational Vehicle. Recreational vehicles operated primarily for personal use."
).

Definition special_school_bus := (Fact
    "School Bus Special",
    "School Buses Require Special Permits",
    "School buses and other vehicles transporting school children for 
    curriculum-related activities: Requires an Illinois School Bus Permit (SBP) 
    and may require a CDL with P and S endorsements. Contact the local school 
    district/bus company for which you plan to drive.
    
    These vehicles may or may not require a CDL, depending on the number of 
    passengers the vehicle is designed to transport or the GVWR of the vehicle. "
).

Definition special_religious := (Fact
    "Religious bus",
    "Religious bus requires restriction",
    "Religious organization vehicles: Requires a J02, J03 or J04 restriction.
    These vehicles may or may not require a CDL, depending on the number of 
    passengers the vehicle is designed to transport or the GVWR of the vehicle. "
).

Definition special_seniors := (Fact
    "Senior bus",
    "Senior bus requires restriction",
    "Vehicles exclusively for transporting senior citizens: Requires a J05, 
    J06 or J07 restriction.  These vehicles may or 
    may not require a CDL, depending on the number of passengers the vehicle 
    is designed to transport or the GVWR of the vehicle. "
).

Definition nonprofit_sharing := (Fact
    "Nonprofit sharing",
    "Nonprofit ride sharing or child care",
    "Non-profit ride sharing or child care vehicles. These vehicles may or 
    may not require a CDL, depending on the number of passengers the vehicle 
    is designed to transport or the GVWR of the vehicle. "
).

Definition cdl_class_a := (Fact
    "Class A",
    "CDL Class A Endorsement",
    "A vehicle with a GCVWR over 26,000 lbs and the towed vehicle GVWR is 
    over 10,000 lbs").
Definition cdl_class_b := (Fact 
    "Class B",
    "CDL Class B Endorsement",
    "A vehicle with a GVWR over 26,000 lbs or a vehicle towing another in excess
    of 10,000 lbs").
Definition cdl_class_c := (Fact
    "Class C",
    "CDL Class C Endorsement",
    "A single vehicle with a GVWR over 16,000 lbs up to 26,000 lbs").
Definition cdl_class_d := (Fact
    "Class D",
    "CDL Class C Endorsement",
    "A single vehicle with a GVWR up to 16,000 lbs").
Definition endorse_p := (Fact
    "P Endorsement",
    "CDL P Endorsement",
    "Applies to the CDL and CLP, is a passenger vehicle endorsement.").
Definition endorse_n := (Fact
    "N Endorsement",
    "CDL N Endorsement",
    "Applies to the CDL and CLP, is a tanker vehicle endorsement.").
Definition endorse_s := (Fact
    "S Endorsement",
    "CDL S Endorsement",
    "Applies to the CDL and CLP, is a school bus vehicle endorsement.").
Definition endorse_h := (Fact
    "H Endorsement",
    "CDL H Endorsement",
    "Applies to the CDL onlt, is a hazardous material endorsement.").
Definition endorse_x := (Fact
    "X Endorsement",
    "CDL X Endorsement",
    "Applies to the CDL only, is a combined tanker and hazardous 
    materials endorsement.").
Definition endorse_t := (Fact
    "T Endorsement",
    "CDL T Endorsement",
    "Applies to the CDL Class A only, is a double or tripple vehicle endorsement.").
Definition endorse_c := (Fact
    "C Endorsement",
    "CDL C Endorsement",
    "Applies to the CDL only, is a charter bus vehicle endorsement.").

Definition restrict_b := (Fact 
    "B Restriction"
    "Corrective Lenses"
    "Requires corrective lenses.  Applies to CDL and CLP.").
Definition restrict_e := (Fact 
    "E Restriction"
    "Automatic Transmission Only"
    "Automatic transmission only in CDL/CMV.").
Definition restrict_f := (Fact 
    "F Restriction"
    "Hearing Aide"
    "Requires outside mirrors or hearing aide.").
Definition restrict_k := (Fact 
    "K Restriction"
    "Intrastate only"
    "Limitted to travel within the state.").
Definition restrict_l := (Fact 
    "L Restriction"
    "Airbrakes forbidden"
    "Air brakes not allowed.").
Definition restrict_m := (Fact 
    "M Restriction"
    "Passenger vehicles"
    "Class B or C passenger vehicles only, applies to CDL.").
Definition restrict_n := (Fact 
    "N Restriction"
    "Passenger vehicles"
    "Class C passenger vehicles only, applies to CDL.").
Definition restrict_o := (Fact 
    "O Restriction"
    "No tractor trailer"
    "No tractor trailer allowed on CDL/CMV, applies to CDL.").
Definition restrict_p := (Fact 
    "P Restriction"
    "No passengers"
    "No passengers allowed in CDL/CMV bus, applies to CLP.").
Definition restrict_v := (Fact 
    "V Restriction"
    "FMCSA"
    "Federal Medical Variance").
Definition restrict_x := (Fact 
    "X Restriction"
    "No cargo"
    "No cargo in a CDL/CMV tank vehicle, CLP only").
Definition restrict_z := (Fact 
    "Z Restriction"
    "No full airbrakes"
    "No full airbrakes equiped in a CDL/CMV tank vehicle, CLP only").
Definition restrict_j10 := (Fact
    "J10 Restriction"
    "CDL Vehicles 16K or less",
    "CDL Vehicles with GVWR 16,000 lbs or Less (Illinois Class C CDL Only)."
).
Definition restrict_j48 := (Fact
    "J48 Restriction"
    "Chool bus"
    "CDL Valid for School Bus Only."
).
Definition restrict_J5_01 := (Fact
    "J50/J51 Restriction"
    "Farm only"
    "Farm Waived Truck Tractor-semi Trailer Vehicles (visit ilsos.gov for 
    definition and eligibility Illinois Non-CDL Class A Only)."
).

Definition docs_required := (Fact
    "Docs Required for CDL/CLP"
    "Docs Required for CDL/CLP"
    "As is required for any driver's license, all new or transferring CDL 
    applicants are required to show documentation verifying their identity, 
    date of birth, Illinois residency, signature and Social Security number. 
    For the most up-to-date list of acceptable documents, please visit 
    ilsos.gov.").

Definition docs_required_citizen := (Fact
    "Citizen Proof Required for CDL/CLP"
    "Citizen Proof Required for CDL/CLP"
    "Effective July 1, 2015, federal law requires all new CDL and CLP applicants 
    to provide proof of citizenship or lawful presence. Existing CDL holders 
    renewing or upgrading their CDL must also provide proof of citizenship or 
    lawful presence to the driver facility staff to be able to renew or upgrade. 
    Refer to the above website for acceptable citizenship (certified birth 
    certificate or valid passport) and lawful presence documents.").

Definition docs_required_medical := (Fact
    "Medical Docs for CDL/CMV"
    "Medical Docs for CDL/CMV"
    "Most operators of commercial vehicles with a gross motor vehicle weight of 
    10,001 pounds or more are required to carry a Medical Examiner’s Certificate 
    at all times while operating a second division vehicle. All non-excepted 
    interstate drivers are required to submit their medical examiner's certificate 
    to the Secretary of State. For additional medical examiner reporting requirements 
    and information, please refer to Section 15.").

Definition medical_card_required := (Fact
    "DOT Medical card required"
    "DOT Medical card required"
    "Yes, if you are a non-excepted driver who will:
        • Operate a commercial vehicle with a gross vehicle weight rating (GVWR) 
        or a gross  combination weight rating (GCWR) of 10,001 pounds or more in 
        the furtherance of a commercial enterprise (private or for hire).
        • Operate a passenger-carrying vehicle designed to transport eight or 
        more passengers, including the driver.
        • Operate any vehicle transporting hazardous materials of a quantity that 
        would require placarding.").

Definition nid := (Abbreviation "NID", "Non-excempt interstate drivers").

Definition medical_cert := (Fact 
    "CDL Medical Certification"
    "CDL Medical Certification"
    "Starting June 30, 2025, all medical certifications with the Secretary of 
    State's office can only be processed through a medical examiner registered 
    with the National Registry (refer to Section 15). All changes and renewals 
    to your medical certification will be transmitted electronically to our 
    office directly from the National Registry.

    If you are a Non-Excepted Interstate (NI) driver, you must renew your current 
    medical certificate directly through a medical examiner registered with the 
    National Registry upon its expiration. You will receive a reminder letter 90 
    days before your current medical certificate expires. If your medical 
    certificate expires and you have not changed your medical certification 
    category status with the Secretary of State, your CDL driving privileges will 
    be canceled. If you have questions about the CDL Medical Program, call 
    217-785-3002 and select Option 3, then Option 5.

    The Secretary of State's office does not regulate or enforce these federal 
    or state medical program rules, except for recording the self-certification 
    of CLP or CDL holders and medical information for NI drivers. The Illinois 
    State Police and IDOT handle enforcement.").

Definition other_requirements := (Fact 
    ""
    ""
    "In addition, commercial vehicle drivers must:
        • Maintain and have in their possession a file that contains their written 
        exam verification, driving exam verification and other records.
        • Be at least age 21 to drive a commercial motor vehicle involved in 
        interstate commerce or transport passengers.
        • Be at least age 18 to obtain a CLP/CDL and/or to transport hazardous 
        materials intrastate (within Illinois only).
        • Certify that they do not have more than one driver’s license and that 
        their driving privileges are not suspended, revoked, canceled or 
        disqualified.
        • Certify that they meet the medical requirements of the Federal Motor 
        Carrier Safety Regulations or that they are not subject to the 
        regulations.").

Definition transfer_requirements := (Fact 
    ""
    ""
    "CDL Transfer and CLP Requirements
        • Applicants for an Illinois CDL–who hold a valid or expired less than 
        one-year CDL issued by another state of the same classification and 
        containing the same endorsements as being applied for in Illinois–are 
        exempted from completing the CDL written examinations, excluding a 
        hazardous materials endorsement. Applicants for an Illinois CDL who hold 
        a valid CDL issued by another state of the same classification and 
        containing the same endorsements as being applied for in Illinois are 
        exempted from the pre-trip/skills/driving testing, unless the applicant 
        is 75 years of age or older, in which case the applicant must complete 
        the pre-trip/skills/driving testing.

        A CDL applicant who wishes to upgrade the classification or to add an 
        endorsement shall be required to take all applicable written and road exams.
        • A CLP issued to an applicant to upgrade to a higher class CDL, remove 
        the air brakes restriction, or add a passenger endorsement or a School 
        Bus endorsement must be held for at least 14 days before the skills/drive 
        testing can be conducted.
        • Upon re-issuance of a CLP, all applicable CDL written exams must be 
        retaken, and any completed skills/drive testing must be re-taken as well 
        as applicable CDL written exams. All CLP re-issuances will require the 
        full CLP fee"
).

Definition mcsia_rule := (Fact 
    "MCSIA Rule"
    "MCSIA Rule"
    "All CDL holders are required by federal law to submit to a one-time 10-year 
    driving history check on renewal or surrender of an out-of-state license to 
    obtain an Illinois CDL. CDL holders applying for a corrected or duplicate 
    license also are required to submit to a one-time 10-year driving history 
    check.").

Definition mcsia := (Abbreviation 
    "MCSIA" "Motor Carrier Safety Improvement Act of 1999").

Definition fees_xfer := (Fact 
    "Renewal and transfer fee"
    "Renewal and transger fee"
    "Is $60 for people under age 69, and less for those over 69").

Definition fees_clp := (Fact
    "The CLP Fee"
    "The CLP Fee"
    "The fee for issuing or re-issuing a CLP is $50").

Definition fees_upgrade := (Fact 
    "Upgrade endorsement mod"
    "Upgrade endorsement mod"
    "The fee to upgrade a CDL/CLP or add/remove an endorsement is $5").

Definition cdl_exam_core := (Fact
    "CDL Core Exam",
    "CDL Core Exam",
    "The Core CDL exam consists of 30 multiple choice questions.  Any CDL holder
    must score 80% or higher (6 questions wrong) in order to pass").

Definition cdl_exam_combi := (Fact
    "CDL Combination Exam",
    "CDL Combination Exam",
    "For the CDL Combination/Articulated vehicle there are 20 questions").
Definition cdl_exam_air := (Fact
    "CDL Air Brakes Exam",
    "CDL Air Brakes Exam",
    "For the CDL Air Brakes exam vehicle there are 25 questions").
Definition cdl_exam_passenger := (Fact
    "CDL Passenger Exam",
    "CDL Passenger Exam",
    "For the CDL Passenger exam there are 20 questions").
Definition cdl_exam_tank := (Fact
    "CDL Tank Exam",
    "CDL Tank Exam",
    "For the CDL Tank exam there are 20 questions").
Definition cdl_exam_school_bus := (Fact
    "CDL School Bus Exam",
    "CDL School Bus Exam",
    "For the CDL School Bus exam there are 20 questions").
Definition cdl_exam_hazzard := (Fact
    "CDL Hazzard Exam",
    "CDL Hazzard Exam",
    "For the CDL Hazzard exam there are 30 questions").
Definition cdl_exam_tripples := (Fact
    "CDL Double/Tripples Exam",
    "CDL Double/Tripples Exam",
    "For the CDL Double/Tripples exam there are 20 questions").
Definition cdl_exam_charter := (Fact
    "CDL Charter Bus Exam",
    "CDL Charter Bus Exam",
    "For the CDL Charter Bus exam there are 20 questions").

Print endorse_h.

Definition cdl_tests := (Fact
    "CDL Tests"
    "CDL Hash 3 tests"
    "There is a pre-inspection test, the basic vehicle controls test,
    and the on the road test.").

Definition cdl_tests_pretrip := (Fact
    "Pre-trip inspection test"
    "Pre-trip inspection test"
    "is conducted to determine whether the applicant knows how to properly inspect 
    the vehicle to determine if it is safe to drive. Applicants will be asked to 
    conduct a pre-trip inspection of a representative vehicle they will operate 
    on the job. The examiner will inquire about a certain area on the vehicle(s), 
    and the applicant must explain what is to be inspected and why. Applicants 
    will be scored section by section of the vehicle, and an applicant who 
    accumulates a predetermined amount of points for a particular section will 
    fail the pre-trip inspection. Applicants will not be tested on any component 
    or area that is not present on the vehicle used for the test, nor will they be 
    required to get under the vehicle to examine any components; however, they must 
    point out these components and explain why it is necessary to inspect those 
    components. If a component of the vehicle examined during the pre-trip 
    inspection fails to work properly through no fault of the applicant, the test 
    may be discontinued, but the vehicle component failure will not be scored 
    against the applicant. If the driver will be operating a vehicle with air 
    brakes while on the job, the test vehicle must be equipped with air brakes. 
    See Sections 2.1 and 12 of this study guide for additional information 
    regarding the pre-trip inspection."
).

Definition cdl_tests_control := (Fact
    "Basic Vehicle Control"
    "Basic Vehicle Control"
    "Basic vehicle control skills test is conducted to evaluate an applicant's 
    ability to use basic skills to control the vehicle. All applicants must 
    complete three exercises on the facility course/road marked by parallel 
    lines, traffic cones or similar boundaries. These exercises test the 
    applicant's ability to move the vehicle forward, parallel park the vehicle, 
    move backward to reverse offset lane. Applicants are scored on how well they 
    stay within the boundaries outlined by the examiner, how many pull-ups and 
    looks are used and how well they maneuver the vehicle into its final position. 
    Applicants should avoid contact with any cones or boundary lines and should 
    not cause a dangerous action within the testing area or exceed the accumulated 
    overall point limit").

Definition cdl_tests_road := (Fact 
    "On-road Driving"
    "On-road Driving"
    "On-road driving test is conducted to evaluate the applicant’s ability to 
    drive safely in a variety of on-road situations. The road test route will 
    include left and right turns, intersections, railway crossings, curves, 
    upgrades, downgrades, rural or semi-rural routes, multilane city streets 
    and/or expressway driving. Applicants will be scored on each of these 
    driving maneuvers and conditions. They must not exceed a predetermined 
    number of points assigned to the driving exam, cause any dangerous action 
    or violate any laws during the exam. Any driver who fails the road test six 
    times will be required to submit an Illinois medical report before attempting 
    any additional road exams.").

Definition cdl_tests_fail_three := (Fact
    "Three-time Fail Rule"
    "Three-time Fail Rule"
    "CDL applicants who fail any particular CDL test three times are required 
    to wait 30 days from the date of the third failed test before retaking the 
    particular test. Three additional failures (six total failures) of the same 
    exam will result in a 90-day waiting period. Three more additional failures 
    (nine total failures) of the same test after the 90-day waiting period will 
    result in a one-year waiting period from the date of the last failed test. 
    The waiting periods apply only to the particular exam that was failed three 
    times. Applicants are allowed three attempts to pass each required exam per 
    fee paid. If an applicant fails any particular test three times, the 
    original fee paid to start the testing will be required to be repaid to 
    resume testing if the applicant needs to pass the failed test to have the 
    CDL issued.").

Definition cdl_cheating_bribes := (Fact
    "Cheating and Bribery."
    "Cheating/Unauthorized Items in the Testing Area/Bribery."
    "Any person found cheating on any portion of a written exam will be given 
    an automatic fail for that exam. In addition, the person will be prohibited 
    from retaking the particular test for a period of 30 days. “Cheating” is 
    defined as receiving or using unauthorized assistance in taking any portion 
    of a test, including, but not limited to, the use of technology, notes, 
    books or written information.

    Cellphones or other electronic devices are not permitted to be powered on, 
    nor are any written items to be present within the testing area. Anyone not 
    adhering to this testing policy will be considered attempting to utilize 
    unauthorized assistance, and the penalties will apply.

    Any person convicted of offering a bribe to any examiner or anyone authorized 
    by law to provide driving instructions or administer driver’s license exams 
    may have their driving privileges suspended or withheld for 120 days. The 
    offense is a Class 2 felony, which carries a three- to seven-year prison 
    sentence and fines of up to $25,000.").

Definition cdl_disqual := (Fact
    "CDL Disqualifications"
    "Don't fuck it up by getting a DUI or in a car accident"
    "All traffic issues, except parking, will generally cause disqualifications
    or suspencions or complete revocal for life (if more than one major offence)
    is committed.  Otherwise the disqualifications generally follow a 30 day,
    90 day, 180 day, and 3 year increments").

Definition other_cdl_rules_no_radar := (Fact
    "No Radar Detectors"
    "No Radar Detectors"
    "No radar detectors anywhere in the truck").

Definition other_cdl_rules_gps := (Fact
    "GPS Rules"
    "GPS Rules"
    "Use GPS specifically designed for truckers, it provides truck specific 
    routes.  Commercial devices could provide bad routes.").

Definition size_rules_obey := (Fact
    "Obey locals"
    "Obey locals"
    "Obey local limitations.  Some bridges or roads may not allow trucks of
    a certain size or weight.").

Definition size_rules_width := (Fact
    "Max is 8 ft 6 in"
    "Max is 8 ft 6 in"
    "Max is 8 ft 6 in with the following exceptions:
        - Farm trucks and equipment when driving after dusk and before dusk.
        - City buses operating within the city limits.
    ").

Definition size_rules_length := (Fact
    "Max vehicle length"
    "Max vehicle length"
    "No single with or without a load, except semitrailer, shall exceed 42 feed.
    Semitrailers can be 53 feet in length, including the load.").

Definition size_rules_length_class_1_2 := (Fact
    "Class I and II Highways"
    "Class I and II Highways"
    "On class I and II highways there is no maximum length limit except for semitrailers
    over 48 ft in length which is 45 feet 6 inches from kingpin to rear axle.
    The maximum length of a trailer or semitrailer in a double is 28 ft 6 in.").

Definition size_rules_length_class_3 := (Fact
    "Class III Highways"
    "Class III Highways"
    "On Class III designated state and local highways the maximum bumper to bumper
    length of tractor semitrailer combinations is 65 ft.  For semitrailers longer
    than 48 feet in length the maximum length from kingpin to rear axle is 42 feet
    6 inches.  All other vehicle combinations are limited to 60 ft in lengh, 
    including load").

Definition size_rules_length_undesignated := (Fact
    "Undesignated local roads"
    "Undesignated local roads"
    "In non-designated local streets the maximum overall length is 55 ft (bumber to
    bumper) including trucks and semitrailer combinations.  It's 60 ft for all
    other types of vehicle combinations").

Definition size_rule_except_pipes := (Fact
    "Non-work days and Pipes"
    "Non-work days and Pipes"
    "On Saturdays, Sundays, and holidays when it's in the daytime and poles, pipes,
    or other objects structural in nature that cannot be disassembled are 
    transported, the can be up to 80 ft and the vehicle and object combo can't be
    more than 100 ft in length").
Definition size_rule_except_stinger := (Fact
    "Stinger haulers"
    "Stinger haulers"
    "Stinger-steered vehicles intended to haul cars or boats can be 80 ft in length
    including a 4 ft overhang in front and 6 ft in rear on class I and II 
    highways.").
Definition size_rule_except_haulers := (Fact
    "Car haulers"
    "Car haulers"
    "On Class I and II highways regular car haulers can be 65 feet including 
    overhang.  On all other highways they must be 60 ft.").

Definition size_rule_height := (Fact
    "Max height"
    "Max height"
    "Max height on all highways is 13 ft 6 in").

Definition access_highway := (Fact
    "Access 1 mile"
    "Access 1 mile"
    "All vehicles operating on Class I highways shall have access up to 1 mile for
    loading/unloading, food, fuel, and rest.").

Definition access_highway_state := (Fact
    "Access 5 miles"
    "Access 5 miles"
    "All vehicles operating on designated state highways shall have 5 mile access
    to loading/unloading, and ammenities.").

Definition size_rule_weight_single := (Fact
    "Single Axle Max Weight"
    "Single Axle Max Weight"
    "Single Axle Max Weight shall be 20,000").

Definition size_rule_weight_tandem := (Fact
    "Tandem axle"
    "Tandem axle"
    "Tabden axle max weight shall be 34,000").

Definition size_rule_weight_quintuple := (Fact
    "Quintuple axle"
    "Quintuple axle"
    "Quintuple axle max weight shall be 80,000 depending on axle spacing").

Definition lighting_sec_div := (Fact
    "Big vehicles require lights"
    "Second division and combination vehicles"
    "Second vision and combination vehicles over 25 feet and wider than 80
    inches must have
        - Two yellow amber lights on the front of the vehicle.
          The lights must be in the upper right corner and visible for 500 ft.
        - Three red lights in the rear of the vehicle in a horizontal line and
          visible for 500 ft.
        - Two yellow amber reflectors on the front of the vehicle.  One reflector
          must be on each of the bottom corners.
        - Two red reflectors on the back lower corner no more than 12 inches away
          from said corner.").
Definition lighting_sec_div_3k := (Fact
    "Long and fat"
    "Second divison vehicles longer than 20 and more than 3K lbs"
    "Second divison vehicles longer than 20 feet and more than 3,000 lbs must have
    special IDOT approved reflectors
        - Two amber reflectors on the side of the vehicle no more than 5 ft above
          the road and placed 1/3 the length of the side of the vehicle.
        - One amber reflector on each side of the vehicle no more than 12 inches
          from the front and not more than 5 ft above the road.
        - One red reflector on each side of the vehicle no more than 12 inches
        from the rear and no more than 5 ft above the road.").

Definition lighting_sec_div_less := (Fact
    ""
    ""
    "").

End Section1.