open util / boolean
 
------SIGNATURE------
//abstract signature for a generic user. It will be extended
abstract sig User{
   age: Int,
   hasVisit: set Visit,
   hasReservation: set Reservation
}

sig SmartUser extends User 
{
hasPosition: lone Position,
hasApp: Bool
}{
hasApp = True
}

sig MobileUser extends User
{
number:  phoneNum,
hasApp: Bool
}{
hasApp = False
}

one sig Date
{
day : String,
time : Time
}
{
day in ("Monday"+"Tuesday"+"Wednesday"+"Thursday"+"Friday"+"Saturday"+"Sunday")
}

sig phoneNum{}
sig Position{}


sig Visit{
     hasSize: Size,
     startTime:  Time,
     endTime: Time,
	ID_code:  QRCode
}{
startTime.minutes in (0+30)
endTime.minutes in (0+30)
startTime.seconds = 0
endTime.seconds = 0
}

sig Reservation{
	hasSize: Size,
	ID_code:  QRCode,
	reservationTime : Time,
	numberInQueue: lone Int
}
//Size bag for a grocery shopping
sig Size{
	dimension : String
}{dimension in ("Small"+"Medium"+"Large")}


sig QRCode{
	isSubmitted: Bool, 
	isValid: Bool
}

//List of the Users who are wiaitng to enter in the market
sig Queue{
listOfReser : set Reservation
}

//List of Users that has scheduled a Visit 
one sig VisitSchedule{
listOfVisits : set Visit
}

one sig Market 
{
userInShop : set User,
state: String
}
{
state in ("Opened"+"Closed")
}

sig Time
{
hours: Int ,
minutes : Int,
seconds: Int
}
{
hours > 0 and hours <=24
minutes >=0 and minutes < 60
seconds >=0 and seconds < 60
}



----PREDICATE----
pred reservePrec [ t1 : Time , t2 : Time]
{
t1.hours < t2.hours or ( t1.hours = t2.hours and t1.minutes < t2.minutes) or  ( t1.hours = t2.hours and t1.minutes = t2.minutes and t1.seconds <= t2.seconds)  
}

pred showReservation{
Market.state = "Opened"
#SmartUser = 2
#MobileUser = 1
#Visit =0
#Reservation = 3
#Queue = 1
#Queue.listOfReser = 2
}

pred showVisit{
#Market.userInShop > 0
Market.state = "Opened"
#SmartUser = 1
#MobileUser = 1
#Visit = 2
#VisitSchedule.listOfVisits = 1
#Reservation=0
#Queue = 0
}

pred showMarketOpened{
Market.state = "Opened"
#SmartUser = 2
#MobileUser = 2
#Visit >0
#Reservation> 2
#Queue = 1
#Queue.listOfReser >1
}



pred showMarketClosed{
Market.state = "Closed"

}


pred addInQueue[q, q2 :Queue, r: Reservation]
{
q2.listOfReser = q.listOfReser + r
#q2.listOfReser = add[#q.listOfReser,1]
}

pred showAdd[q, q2:Queue, r: Reservation]
{
#Queue = 2
 addInQueue[q,q2, r]
#Reservation > 1
#q.listOfReser > 1
}

pred delInQueue[q, q2 :Queue, r: Reservation, u: SmartUser, u2 : SmartUser]
{
r in u.hasReservation and r in q.listOfReser
u2.hasReservation = u.hasReservation - r
u2.hasVisit = u.hasVisit
u2.age = u.age
u2.hasPosition = u.hasPosition
q2.listOfReser = q.listOfReser - r
#q2.listOfReser = sub[#q.listOfReser,1]
}

pred showDel[q, q2:Queue, r: Reservation, u: SmartUser, u2 : SmartUser]
{
#Queue = 2
 delInQueue[q,q2, r,u,u2]
#Reservation > 1
#q.listOfReser > 1
}


----FACT----

// The Reservation can be booked only when the shop is opened
fact onlyInOpenTime
{
all r: Reservation | r.reservationTime.hours > 8 and r.reservationTime.hours < 20
all v: Visit | v.startTime.hours > 8 and v.endTime.hours < 20 and reservePrec[v.startTime,v.endTime]
}


// A Visit is accepted by the reader if and only if 
fact visitAccepted
{
all v: Visit |   (v.ID_code.isSubmitted = True and  v.ID_code.isValid = True)  <=> (reservePrec[v.startTime,Date.time] and  reservePrec[Date.time,v.endTime])
} 


// Condition for a Visit finished
fact visitFinish
{
all v: Visit |   (v.ID_code.isSubmitted = True and  v.ID_code.isValid = False)  <=> reservePrec[v.endTime,Date.time]
} 

// Condition for a Visit not started yet
fact visitEarly
{
all v: Visit |   (v.ID_code.isSubmitted = False and  v.ID_code.isValid = True)  <=> reservePrec[Date.time,v.startTime] 
} 


// The reservation time cannot exceed data time
fact reservationNotInFuture
{
all r : Reservation | reservePrec[r.reservationTime,Date.time]
}

//  Every User must have at most 1 Reservation active
fact sameMomentReserv
{
no r1 : Reservation, r2 : Reservation | r1.reservationTime = r2.reservationTime and r1 not = r2
}

//Function that returns the number of user in queue before r1 (r1 included)
fun numberQueue [r1: Reservation] : set Reservation {
{  r: Reservation | r.ID_code.isSubmitted = False and r.ID_code.isValid = True and  reservePrec[r.reservationTime, r1.reservationTime] }

}

//Assign the queue's cardinality to itself
fact cardinalityQueue {
all r: Queue.listOfReser |  r.numberInQueue = #numberQueue[r]
}


//Assign none if a Reservation is not in queue
fact reservationQueue
{
all r: ( Reservation - Queue.listOfReser ) | r.numberInQueue = none
}


//For each Visit assignes time slot based on the bag size
fact visitSlot
{
all v: Visit | v.hasSize.dimension = "Small" <=>  ((  minus[v.endTime.hours,v.startTime.hours]= 1 and  (v.startTime.minutes - v.endTime.minutes) = 30 ) or (( v.endTime.hours = v.startTime.hours) and minus[v.endTime.minutes, v.startTime.minutes] = 30 ))
all v1: Visit | v1.hasSize.dimension = "Medium" <=>  (( minus[v1.endTime.hours,v1.startTime.hours] = 1 ) and  v1.startTime.minutes = v1.endTime.minutes )
all v2: Visit | v2.hasSize.dimension = "Large" implies  (( minus[v2.endTime.hours, v2.startTime.hours] = 2 and  minus[v2.startTime.minutes, v2.endTime.minutes] = 30 ) or (minus[ v2.endTime.hours ,v2.startTime.hours] = 1 and minus[v2.endTime.minutes ,v2.startTime.minutes] = 30 ))
}




// When the market is closed the number of people in the market is equal to 0
fact marketClose
{
Market.state = "Closed" implies ( #User = 0 )
}

// For each User only one QRCode is valid and submitted at each time
fact sserOneActive{
all u : User | lone h : (u.hasVisit.ID_code + u.hasReservation.ID_code ) | h.isSubmitted = True and h.isValid = True
}

// Condition for a User to be in the Market
fact userInShop{
all u :  Market.userInShop  | one q : QRCode | q in ( u.hasVisit.ID_code + u.hasReservation.ID_code) and q.isSubmitted = True and q.isValid = True 
}

fact userInShop2 
{
no u: (User - Market.userInShop) | one q : QRCode |   q in ( u.hasVisit.ID_code + u.hasReservation.ID_code) and q.isSubmitted = True and q.isValid = True 

}

// It doesn't exist a QrCode not valid and not submitted
fact notExistQR_codeMalevolus{
no q : QRCode | q.isSubmitted = False and q.isValid = False
}

//Every position is associated to a SmartUser
fact smartUserCanOwnPosition 
{
all p : Position | one su : SmartUser |  p in su.hasPosition
}


fact openMarket
{
Market.state = "Opened" <=> (Date.day in ("Monday"+"Tuesday"+"Wednesday"+"Thursday"+"Friday") and Date.time.hours > 8 and Date.time.hours < 20 )
}

fact closeMarket
{
not Market.state ="Opened" implies Market.state ="Closed"
}

fact uniqNumber 
{
all pn : phoneNum | one mb : MobileUser |  pn in mb.number
}


fact noUnderAge
{
all u : User | u.age > 18 and u.age < 100
}

// Each Visit belongs to one User
fact visitBelongUser
{
all v : Visit | one u1 : User | v in u1.hasVisit 
}

// Each User must have at most one Visit active
fact only1VisitActive
{
all u : User |  lone v1 : Visit |  v1 in u.hasVisit and v1.ID_code.isValid = True 
}

// Condition for a Visit to be scheduled
fact visitInSchedule
{
all v : Visit | (v.ID_code.isValid = True and v.ID_code.isSubmitted= False) <=> ( v in VisitSchedule.listOfVisits)
}

// Each Reservation belongs to one User
fact reservBelongUser
{
all r : Reservation | one u : User | r in u.hasReservation
}

// Each User must have at most one Reservation active
fact only1ReservationActive 
{
all u : User | lone r : Reservation | r in u.hasReservation and r.ID_code.isValid = True
}

// Condition for a Rservation to be insterted in the Queue
fact reservationQueue
{
all r : Reservation |  ( r.ID_code.isSubmitted = False and r.ID_code.isValid = True ) <=> ( r in Queue.listOfReser )
}

// For each booking the QRCode is unique
fact oneQRforVisit {
all q : QRCode | (q in Visit.ID_code or q in Reservation.ID_code)
no v1 : Visit, v2 : Visit | v1.ID_code = v2.ID_code and v1 not = v2
no r1 : Reservation, r2 : Reservation | r1.ID_code = r2.ID_code and r1 not = r2
no r : Reservation, v: Visit | v.ID_code = r.ID_code
}
---------------------------------------------------------

--<LET>

//Cardinality of QRCode submitted and valid
let many [QRCode] = {
 q: QRCode | q.isValid = True and q.isSubmitted=True 
}

--</LET>
---------------------------------------------------------


--<ASSERT>
//Check that user in shop are equal to person that have a QRCode valid and submitted
assert totPerson{
#Market.userInShop = #many[QRCode]
}

//Check that if the market is closed implies that there are no users with either Reservation or Visit submitted and valid
assert noBooking{
Market.state = "Closed" implies #{Visit + Reservation} = 0
}





--</ASSERT>--
/*	
	check totPerson
	check noBooking 
*/

run showMarketOpened  for 8 but  8 Int
/* 
	run showMarketClosed for  8 Int
   	run showReservation for 8 but  8 Int
  	run showVisit for 6 Int
	run showAdd for 6 Int
	run showDel for 6 Int
*/
