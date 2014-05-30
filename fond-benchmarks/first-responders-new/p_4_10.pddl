(define (problem FR_4_10)
 (:domain first-response)
 (:objects  l1 l2 l3 l4  - location
	    f1 f2 f3 f4 - fire_unit
	    v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 - victim
	    m1 m2 m3 m4 - medical_unit
)
 (:init 
	;;strategic locations
     (hospital l2)
     (hospital l3)
     (hospital l2)
     (hospital l1)
     (water-at l4)
	;;disaster info
     (fire l1)
     (victim-at v1 l4)
     (victim-status v1 hurt)
     (fire l3)
     (victim-at v2 l2)
     (victim-status v2 hurt)
     (fire l1)
     (victim-at v3 l4)
     (victim-status v3 hurt)
     (fire l1)
     (victim-at v4 l4)
     (victim-status v4 hurt)
     (fire l3)
     (victim-at v5 l1)
     (victim-status v5 hurt)
     (fire l3)
     (victim-at v6 l2)
     (victim-status v6 hurt)
     (fire l1)
     (victim-at v7 l2)
     (victim-status v7 hurt)
     (fire l1)
     (victim-at v8 l4)
     (victim-status v8 hurt)
     (fire l1)
     (victim-at v9 l3)
     (victim-status v9 hurt)
     (fire l1)
     (victim-at v10 l2)
     (victim-status v10 hurt)
	;;map info
	(adjacent l1 l1)
	(adjacent l2 l2)
	(adjacent l3 l3)
	(adjacent l4 l4)
   (adjacent l1 l1)
   (adjacent l1 l1)
   (adjacent l3 l1)
   (adjacent l1 l3)
   (adjacent l3 l2)
   (adjacent l2 l3)
   (adjacent l3 l3)
   (adjacent l3 l3)
	(fire-unit-at f1 l2)
	(fire-unit-at f2 l3)
	(fire-unit-at f3 l4)
	(fire-unit-at f4 l2)
	(medical-unit-at m1 l4)
	(medical-unit-at m2 l2)
	(medical-unit-at m3 l4)
	(medical-unit-at m4 l2)
	)
 (:goal (and  (nfire l1) (nfire l3) (nfire l1) (nfire l1) (nfire l3) (nfire l3) (nfire l1) (nfire l1) (nfire l1) (nfire l1)  (victim-status v1 healthy) (victim-status v2 healthy) (victim-status v3 healthy) (victim-status v4 healthy) (victim-status v5 healthy) (victim-status v6 healthy) (victim-status v7 healthy) (victim-status v8 healthy) (victim-status v9 healthy) (victim-status v10 healthy)))
 )