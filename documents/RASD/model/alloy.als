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
	numberInQueue: Int
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
one sig Queue{
listOfReser : some Reservation
}

//List of Users that has scheduled a Visit 
one sig VisitSchedule{
listOfVisits : Visit
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

----------------------------------------------------------------------------------------------------------------------

----PREDICATE----
pred ReservePrec [ t1 : Time , t2 : Time]
{
t1.hours < t2.hours or ( t1.hours = t2.hours and t1.minutes < t2.minutes) or  ( t1.hours = t2.hours and t1.minutes = t2.minutes and t1.seconds <= t2.seconds)  
}

pred show {
--#listOfReser = 4
}


----FACT----

// The Reservation can be booked only when the shop is opened
fact onlyInOpenTime
{
all r: Reservation | r.reservationTime.hours > 8 and r.reservationTime.hours < 20
all v: Visit | v.startTime.hours > 8 and v.endTime.hours < 20 and v.endTime.hours > 8 and v.startTime.hours < 20 
}

// A visit the startTime is always minor than the endTime
fact VisitTime
{
all v: Visit | ReservePrec[v.startTime,v.endTime] and (v.endTime.hours - v.startTime.hours <= 1) and (  (v.endTime.hours > v.startTime.hours) or (v.endTime.hours = v.startTime.hours and v.endTime.minutes > v.startTime.minutes) )
}

// A Visit is accepted by the reader if and only if 
fact VisitAccepted
{
all v: Visit |   (v.ID_code.isSubmitted = True and  v.ID_code.isValid = True)  <=> (ReservePrec[v.startTime,Date.time] and  ReservePrec[Date.time,v.endTime])
} 


// Condition for a Visit finished
fact VisitFinish
{
all v: Visit |   (v.ID_code.isSubmitted = True and  v.ID_code.isValid = False)  <=> Rese-rvePrec[v.endTime,Date.time]
} 

// Condition for a Visit not started yet
fact VisitEarly
{
all v: Visit |   (v.ID_code.isSubmitted = False and  v.ID_code.isValid = True)  <=> ReservePrec[Date.time,v.startTime] 
} 


// The reservation time cannot exceed data time
fact ReservationNotInFuture
{
all r : Reservation | ReservePrec[r.reservationTime,Date.time]
}

//  Every User must have at most 1 Reservation active
fact SameMomentReserv
{
no r1 : Reservation, r2 : Reservation | r1.reservationTime = r2.reservationTime and r1 not = r2
}


/**fact qwerty {
all r: Reservation |  r.numberInQueue = #numerocoda[r]
}

fun numerocoda [r1: Reservation] : set Reservation {
{  r: Reservation | r.ID_code.isSubmitted = False and r.ID_code.isValid = True and  ReservePrec[r.reservationTime, r1.reservationTime] }
--{x: Set1 | expr[x]}
}
**/


let many [QRCode] = {
 q: QRCode | q.isValid = True and q.isSubmitted=True }


// When the market is closed the number of people in the market is equal to 0
fact MarketClose
{
Market.state = "Closed" implies ( #User = 0 )
}

// For each User only one QRCode is valid and submitted at each time
fact UserOneActive{
all u : User | one h : (u.hasVisit.ID_code + u.hasReservation.ID_code ) | h.isSubmitted = True and h.isValid = True
}

// Condition for a User to be in the Market
fact UserInShop{
all u : User | lone q : QRCode | ( q in ( u.hasVisit.ID_code + u.hasReservation.ID_code) and  q.isSubmitted = True and q.isValid = True ) <=> ( u in Market.userInShop)
}

// It doesn't exist a QrCode not valid and not submitted
fact notExistQR_codeMalevolus{
no q : QRCode | q.isSubmitted = False and q.isValid = False
}

//Every position is associated to a SmartUser
fact SmartUserCanOwnPosition 
{
all p : Position | one su : SmartUser |  p in su.hasPosition
}


fact OpenMarket
{
Market.state = "Opened" <=> (Date.day in ("Monday"+"Tuesday"+"Wednesday"+"Thursday"+"Friday") and Date.time.hours > 8 and Date.time.hours < 20 )
}

fact CloseMarket
{
not Market.state ="Opened" <=> Market.state ="Closed"
}

fact UniqNumber 
{
all pn : phoneNum | one mb : MobileUser |  pn in mb.number
}


fact noUnderAge
{
--all u : User | u.age > 18 and u.age < 100
}

// Each Visit belongs to one User
fact VisitBelongUser
{
all v : Visit | one u1 : User | v in u1.hasVisit 
}

// Each User must have at most one Visit active
fact Only1VisitActive
{
all u : User |  lone v1 : Visit |  v1 in u.hasVisit and v1.ID_code.isValid = True 
}

// Condition for a Visit to be scheduled
fact VisitInSchedule
{
all v : Visit | (v.ID_code.isValid = True and v.ID_code.isSubmitted= False) <=> ( v in VisitSchedule.listOfVisits)
}

// Each Reservation belongs to one User
fact ReservBelongUser
{
all r : Reservation | one u : User | r in u.hasReservation
}

// Each User must have at most one Reservation active
fact Only1ReservationActive 
{
all u : User | lone r : Reservation | r in u.hasReservation and r.ID_code.isValid = True
}

// Condition for a Rservation to be insterted in the Queue
fact ReservationQueue
{
all r : Reservation |  ( r.ID_code.isSubmitted = False and r.ID_code.isValid = True ) <=> ( r in Queue.listOfReser )
}

// For each booking the QRCode is unique
fact OneQRforVisit {
all q : QRCode | (q in Visit.ID_code or q in Reservation.ID_code)
no v1 : Visit, v2 : Visit | v1.ID_code = v2.ID_code and v1 not = v2
no r1 : Reservation, r2 : Reservation | r1.ID_code = r2.ID_code and r1 not = r2
no r : Reservation, v: Visit | v.ID_code = r.ID_code
}
---------------------------------------------------------

--<ASSERT>
assert totPerson{
#Market.userInShop = #many[QRCode]
}
--</ASSERT>

--check totPerson for 5

run show for 15 but  5 User, 8 Int
