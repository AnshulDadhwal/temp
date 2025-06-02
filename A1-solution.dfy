method Q1(A:bool,B:bool)
{
  ghost var PS: bool;
  PS := (A ==> B) && (!A ==> B);
  PS := (A || !A) ==> B; // A.34
  PS := true ==> B; // A.16
  PS := B; // A.28
}

predicate IsLeapYear(y:nat) {
  y%4 == 0 && (y%100 == 0 ==> y%400==0)
}

function DaysInYear(y:nat): nat{
  if IsLeapYear(y) then 366 else 365
}

ghost function Year(d:nat, y:nat):nat 
{
  if d > DaysInYear(y) then Year(d-DaysInYear(y),y+1) else y
}

method CalculateYear(d: nat) returns (year: nat)
  requires d > 0
  ensures year == Year(d,1980)
{
  ghost var WP: bool;
  ghost var WP_s: bool;
  // method is partially correct since d > 0 ==> d >= 0
  WP := d >= 0; // arithmetic
  WP := d >= 0 && Year(d,1980) == Year(d,1980);
  year:= 1980;
  WP := d >= 0 && Year(d,year) == Year(d,1980);
  var days := d;
  WP := days >= 0 && Year(days,year) == Year(d,1980);
  while days > 365
    invariant days >= 0 && Year(days,year) == Year(d,1980)
  {
    WP := days > 365 && Year(days,year) == Year(d,1980); // Q1 twice
    WP := days > 365 &&
          (IsLeapYear(year) ==> (days > 366 ==> Year(days,year) == Year(d,1980)) &&
                                (days <= 366 ==> Year(days,year) == Year(d,1980))) &&
          (!IsLeapYear(year) ==> Year(days,year) == Year(d,1980));
    // arithmetic (days <= 366 is equivalent to days == 366 when days > 365)
    WP := days > 365 &&
          (IsLeapYear(year) ==> (days > 366 ==> Year(days,year) == Year(d,1980)) &&
                                (days == 366 ==> Year(days,year) == Year(d,1980))) &&
          (!IsLeapYear(year) ==> Year(days,year) == Year(d,1980));
    // Year(0,year)=Year(366,year) for leap year
    WP := days > 365 &&
          (IsLeapYear(year) ==> (days > 366 ==> Year(days,year) == Year(d,1980)) &&
                                (days == 366 ==> Year(0,year) == Year(d,1980))) &&
          (!IsLeapYear(year) ==> Year(days,year) == Year(d,1980));
    // Year(d-DaysInYear(y),y+1)==Year(d,y) when d > DaysInYear(y)
    WP := days > 365 &&
            (IsLeapYear(year) ==> (days > 366 ==> Year(days-366,year+1) == Year(d,1980)) &&
                                  (days == 366 ==> Year(0,year) == Year(d,1980))) &&
            (!IsLeapYear(year) ==> Year(days-365,year+1) == Year(d,1980));    
    // arithmetic (days <= 366 is equivalent to days == 366 when days > 365, and 
    // days - 365 >= 0 is true when days > 365)
    WP_s := days > 365 &&
            (IsLeapYear(year) ==> (days > 366 ==> Year(days-366,year+1) == Year(d,1980)) &&
                                  (days <= 366 ==> Year(0,year) == Year(d,1980))) &&
            (!IsLeapYear(year) ==> days - 365 >= 0 && Year(days-365,year+1) == Year(d,1980));    
    // strengthen with guard
    WP := (IsLeapYear(year) ==> (days > 366 ==> Year(days-366,year+1) == Year(d,1980)) &&
                                (days <= 366 ==> days == 366 && Year(0,year) == Year(d,1980))) &&
          (!IsLeapYear(year) ==> days - 365 >= 0 && Year(days-365,year+1) == Year(d,1980));
    if IsLeapYear(year) {
      WP := (days > 366 ==> Year(days-366,year+1) == Year(d,1980)) &&
            (days <= 366 ==> days == 366 && Year(0,year) == Year(d,1980));   
      // arithmetic (days - 366 == 0 when days == 366)
      WP := (days > 366 ==> Year(days-366,year+1) == Year(d,1980)) &&
            (days <= 366 ==> days == 366 && Year(days-366,year) == Year(d,1980));   
      // arithmetic (days - 366 >= 0 is equivalent to days == 366 when days <= 366, and 
      // days - 366 >= 0 is true when days > 366)
      WP := (days > 366 ==> days - 366 >= 0 && Year(days-366,year+1) == Year(d,1980)) &&
            (days <= 366 ==> days - 366 >= 0 && Year(days-366,year) == Year(d,1980));
      if days > 366 {
        WP := days - 366 >= 0 && Year(days-366,year+1) == Year(d,1980);
        days := days - 366;
        WP := days >= 0 && Year(days,year+1) == Year(d,1980);
        year := year+1;
        WP := days >= 0 && Year(days,year) == Year(d,1980);
      } else {
        WP := days - 366 >= 0 && Year(days-366,year) == Year(d,1980);
        days := days - 366;
        WP := days >= 0 && Year(days,year) == Year(d,1980) ;
      }
      WP := days >= 0 && Year(days,year) == Year(d,1980);
    } else {
      WP := days - 365 >= 0 && Year(days-365,year+1) == Year(d,1980);
      days := days - 365;
      WP := days >= 0 && Year(days,year+1) == Year(d,1980);
      year:= year + 1;
      WP := days >= 0 && Year(days,year) == Year(d,1980);
    }
    WP := days >= 0 && Year(days,year) == Year(d,1980);
  }
  WP := days <= 365 && days >= 0 && Year(days,year) == Year(d,1980); 
  //Year(days,year)==year when days <= 365
  WP_s := days <= 365 && days >= 0 && year == Year(d,1980); 
  // strengthen with negation of guard and days >= 0
  WP := year == Year(d,1980);
}

method Q3(d: nat) returns (year: nat)
  requires d > 0
  ensures year == Year(d,1980)
{
  year:= 1980;
  var days := d;
  while days > 365
    invariant days >= 0 && Year(days,year) == Year(d,1980)
    decreases days
  {
    ghost var WP: bool;
    ghost var WP_s: bool;
    // termination holds since WP implied by the invariant
    WP := days >= 0;  // Q1
    WP := (IsLeapYear(year) ==> days >= 0) && (!IsLeapYear(year) ==> days >= 0);    //arithmetic
    WP := (IsLeapYear(year) ==> days >= 0 && days > days-366) &&
          (!IsLeapYear(year) ==> days >= 0 && days > days - 365);
    ghost var m := days;
    WP := (IsLeapYear(year) ==> m >= 0 && m > days - 366) &&
          (!IsLeapYear(year) ==> m >= 0 && m > days - 365);
    if IsLeapYear(year) {
      WP :=  m >= 0 && m > days - 366;  // Q1
      WP := (days > 366 ==> m >= 0 && m > days - 366) && (days <= 366 ==> m >= 0 && m > days - 366);
      if days > 366 {
        WP := m >= 0 && m > days - 366;
        days := days - 366;
        WP := m >= 0 && m > days;
        year := year+1;
        WP := m >= 0 && m > days;
      } else {
        WP := m >= 0 && m > days - 366;
        days := days - 366;
        WP := m >= 0 && m > days;
      }
      WP := m >= 0 && m > days;
    } else {
      WP := m >= 0 && m > days - 365;
      days := days - 365;
      WP := m >= 0 && m > days;
      year:= year + 1;
      WP := m >= 0 && m > days;
    }
    WP := m >= 0 && m > days;  // termination metric is days
  }
}