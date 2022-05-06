#include <iostream>
#include <string>
using namespace std;

#include "rac.h"

typedef unsigned int uint;

// RAC begin

//********************************************************************************************
//                                      Absolute Calendar
//********************************************************************************************

// The days of the week are encoded as Sunday = 1, Monday = 2, ...
// The absolute calendar consists of a single month of infinite length.
// We shall arrange for day 1 to be a Sunday, so that the day of the week of a given absolute 
// date may be computed as follows:

uint dayOfWeek(uint day) {
  return day % 7;
}

// A moment in time is a triple (d h p), where d is an absolute date and (h p) is a time 
// of day, measured in hours and parts of an hour, where an hour comprises 1080 parts.
// A day begins at 6PM, which is therefore the moment (d 0 0).
// Such a triple can also represent a duration, i.e., a period of time.
// Thus, 0 <= d, 0 <= h < 24, and 0 <= p < 1080.

struct Moment {uint day; uint hour; uint part;};

// The following adds a duration to a moment:

Moment addTime(Moment x, Moment y) {
  Moment sum;
  uint sumParts = x.part + y.part;
  sum.part = sumParts % 1080;
  uint sumHours = x.hour + y.hour + sumParts/1080;
  sum.hour = sumHours % 24;
  sum.day = x.day + y.day + sumHours/24;
  return sum;
}

// Multiply a duration by a natural number:

Moment mulTime(uint m, Moment x) {
  Moment prod;
  uint prodParts = m * x.part;
  prod.part = prodParts % 1080;
  uint prodHours = m * x.hour + prodParts/1080;
  prod.hour = prodHours % 24;
  prod.day = m * x.day + prodHours/24;
  return prod;
}

// Is the time of day of moment x earlier than a given time of day?

bool earlier (Moment x, uint h, uint p) {
  return x.hour < h || x.hour == h && x.part < p;
}

//********************************************************************************************
//                                       Hebrew Calendar
//********************************************************************************************

// The mean lunar period is approximated as 29 days, 12 hours, 793 parts, or
// 29 days, 12 hours, 44 minutes, 3 1/3 seconds, or about 29.5305941 days.

const Moment Lunation = {29, 12, 793};

// A solar year is about 365.242199 days.  Thus, the average number of months in a calendar year 
// should be close to the ratio 365.242199/29.5305941 = 12.368264.

// The Metonic cycle is based on the observation that this ratio is close to 235/19 = 12.368421.
// Thus, since 235 = 19 * 12 + 7, the calendar is constructed so that any 19-year interval consists
// of 12 12-month "common years" and 7 13-month "leap years", with a total of 235 months:

bool leap(uint year) {
  uint m = year % 19;
  return m == 0 || m == 3 || m == 6 || m == 8 || m == 11 || m == 14 || m == 17;
}

bool common(uint year) {
  return !leap(year);
}

uint monthsInYear(uint year) {
  return leap(year) ? 13 : 12;
}

// The first molad (lunar conjunction), known as Molad Adam, is supposed to have occurred at 8AM 
// (14h 0p) on the 6th day (Friday) of creation.  This was the molad of Tishri of the year 2.  
// Since year 1 is by definition a common year, the (imaginary) molad of Tishri of year 1 is 
// computed to have occurred earlier by 12 lunations, or 354 days, 8 hours, 876 parts, which puts 
// it at 5 hours, 204 parts (just after 11:11 PM) on a Sunday night.  Thus, day 1 of our absolute 
// calendar is set to the preceding day, so that the molad of Tishri of year 1, known as Molad
// Beharad, is 2d 5h 204p.

const Moment Beharad = {2, 5, 204};

// The molad of Tishri of a given year:

Moment molad (uint year) {
  // Compute the total number of months in all preceding years, multiply by the lunation period,
  // and add the product to Beharad:
  uint priorMonths = 0;
  for (uint y=1; y<year; y++) {
    priorMonths += monthsInYear(y);
  }
  return addTime(Beharad, mulTime(priorMonths, Lunation));
}

// Rosh Hashanah is either the day of the molad of Tishri or up to 2 days later, as determined
// by the 4 "dechiyot".  According to the 1st dechiyah, Rosh Hashanah is delayed a day if the
// molad occurs at or after noon.  This may be implemented simply by replacing the molad by
// the "delayed molad", which is defined to occur 6 hours later:

Moment dmolad(uint year) {
  Moment sixHours = {0, 6, 0};
  return addTime(molad(year), sixHours);
}

// According to the 2nd dechiyah, Rosh Hashanah must be delayed a day if the delayed molad
// occurs on a Sunday, Wednesday, or Friday.  The 3rd and 4th are designed to ensure that
// the length of every year is admissible (353, 354, or 355 for a common year; 383, 384, or 385
// for a leap year):

uint roshHashanah(uint year) {
  Moment dm = dmolad(year);
  uint day = dm.day;
  uint dw = dayOfWeek(day);
  if (dw == 1 || dw == 4 || dw == 6) { // 2nd dechiyah
    day++;
  }
  else if (dw == 3 && !earlier(dm, 15, 204) && !leap(year)) { // 3rd dechiyah
    day = day + 2;
  }
  else if (dw == 2 && !earlier(dm, 21, 589) && leap(year - 1)) { // 4th dechiyah
    day++;
  }
  return day;
}

uint yearLength(uint year) {
  return roshHashanah(year + 1) - roshHashanah(year);
}

// The file proof.lisp contains an ACL2 proof of the theorem that every year has an 
// admissible length.

// The months of the year are numbered as follows.  Note that the 12 months of a common year
// are numbered in order, but the extra month of a leap year is number 13 although it is
// inserted between months 5 and 6:

// 1  Tishri                         30
// 2  Cheshvan                       29 or 30
// 3  Kislev                         30 or 29
// 4  Tevat                          29
// 5  Shevat                         30
// 13 Adar I (leap year only)        30
// 6  Adar (Adar II in leap year)    29
// 7  Nisan                          30
// 8  Iyar                           29
// 9  Sivan                          30
// 10 Tammuz                         29
// 11 Av                             30
// 12 Elul                           29
//                                  ----
//                                  353, 354, or 355 (common year)
//                                  383, 384, or 385 (leap year)

// The length of every month is 29 or 30.  The length of each month is fixed except Cheshvan
// and Kislev, which vary in order to accommodate all possible year lengths:

uint monthLength(uint month, uint yearLen) {
  uint monLen;
  switch(month) {
  case 2: monLen = yearLen == 355 || yearLen == 385 ? 30 : 29; break;
  case 3: monLen = yearLen == 353 || yearLen == 383 ? 29 : 30; break;
  default: monLen = month % 2 == 0 ? 29 : 30;
  }
  return monLen;
}

// The molad of a given month, used in the formulation of Landau's theorem, which is also proved
// in proof.lisp: The molad of every month occurs before the end of the 1st day of the month.

Moment monthlyMolad(uint month, uint year) {
  uint priorMonths;
  if (leap(year) && month >= 6) {
    priorMonths = month == 13 ? uint(5) : month;
  }
  else {
    priorMonths = month - 1;
  }
  return addTime(molad(year), mulTime(priorMonths, Lunation));
}

// A date is represented as a triple consisting of day of month, month, and year:

struct Date {uint day; uint month; int year;};

// Conversion from Hebrew date to absolute date:

uint h2a(Date date) {
  // Compute number of days of date.year that precede date.month:
  uint priorDays = 0;
  for (uint m=1; m<date.month && (m<6 || date.month!=13); m++) {
    priorDays+= monthLength(m, yearLength(date.year));
  }
  if (leap(date.year) && date.month >= 6 && date.month != 13) {
    priorDays += 30;
  }
  // Add to that the absolute date of the last day of the preceding year
  // and the day of the month:
  return roshHashanah(date.year) - 1 + priorDays + date.day;
}

// An arbitrary upper bound on the years of interest is assumed.  This is required for ACL2
// termination proofs, but may be ignored for other purposes:

const int yearBound = 100000;

// Conversion from absolute date to Hebrew date:

Date a2h(uint d) {
  Date hdate;
  // Since the absolute date of Rosh Hashanah of year 1 is 2, the absolute date d is the
  // (d - 1)st day from the beginning of year 1:
  d -= 1;
  // The day of interest is now the dth day from the beginning of year 1.
  uint year;
  for (year=1; year < yearBound && d > yearLength(year); year++) {
    d -= yearLength(year);
  }
  hdate.year = year;
  // The day of interest is now the dth day of year.
  uint month;
  uint yearLen = yearLength(year);
  for (month=1; month<=5 && d > monthLength(month, yearLen); month++) {
    d -= monthLength(month, yearLen);
  }
  if (month <= 5) {
    // The day of interest occurs during first 5 months.
  }
  else if (leap(year) && d <= 30) {
    // The day of interest occurs in Adar I of leap year.
    month = 13;
  }
  else {
    if (leap(year)) {
      // Account for Adar I:
      d -= 30;
    }
    // The day of interest is now the dth day, counting from beginning of Adar (or Adar II). 
    for (month=6; month<12 && d > monthLength(month, yearLen); month++) {
      d -= monthLength(month, yearLen);
    }
  }
  hdate.month = month;
  hdate.day = d;
  return hdate;
}

//********************************************************************************************
//                                    Gregorian Calendar
//********************************************************************************************

// The Gregorian calendar is designed to have an average year length that approximates the
// solar cycle of 365.242199 days.  This is achieved with 97 leap years in every 400-year
// cycle, which yields an average of 365 + 97/400 = 365.2425:

bool GregorianLeap(int year) {
  return year % 4 == 0 && (year % 400 == 0 || year % 100 != 0);
}

uint GregorianMonthLength(uint month, uint year) {
  // 30 days hath September, April, June, and November, ...
  if (month == 9 || month == 4 || month == 6 || month == 11) {
    return 30;
  }
  else if (month == 2) {
    return GregorianLeap(year) ? 29 : 28;
  }
  else {
    return 31;
  }
}

uint GregorianYearLength(uint year) {
  return GregorianLeap(year) ? 366 : 365;
}

// Convert a Gregorian date to absolute:

uint g2a(Date date) {
  // The absolute date of Rosh Hashanah of year 1 is 2, which is 7 September -3760.
  // Since -3760 is a leap year, this is 251 days after 31 December -3761, the absolute date
  // of which would have been -249.
  int d = -249;
  // d is now the absolute date of 31 December -3761.
  int year;
  for (year=-3760; year<yearBound && year<date.year; year++) {
    d += GregorianYearLength(year);
  }
  // d is now the absolute date of 31 December of year preceding date.year.
  uint month;
  for (month=1; month<=12 && month<date.month; month++) {
    d += GregorianMonthLength(month, year);
  }
  // d is now the absolute date of the last day of month preceding date.month.
  return d + date.day;
}

// Convert an absolute date to Gregorian:

Date a2g(int d) {
  Date gdate;
  // Absolute date d is the (d + 249)th day from the beginning of -3760:
  d += 249;
  // The day of interest is now the dth day from the beginning of -3760:
  int year;
  for (year=-3760; year<yearBound && d>GregorianYearLength(year); year++) {
    d -= GregorianYearLength(year);
  }
  gdate.year = year;
  // The day of interest is now the dth day of year:
  uint month;
  for (month=1; month <= 12 && d>GregorianMonthLength(month, year); month++) {
    d -= GregorianMonthLength(month, year);
  }
  gdate.month = month;
  gdate.day = d;
  return gdate;
}
 
// Convert between Hebrew and Gregorian dates:

Date h2g(Date date) {
  return a2g(h2a(date));
}

Date g2h(Date date) {
  return a2h(g2a(date));
}

//********************************************************************************************
//                                      Julian Calendar
//********************************************************************************************

// The Julian calendar is basedon an average year length of precidely365.25 days.

bool JulianLeap(int year) {
  return year % 4 == 0;
}

uint JulianMonthLength(uint month, uint year) {
  // 30 days hath September, April, June, and November, ...
  if (month == 9 || month == 4 || month == 6 || month == 11) {
    return 30;
  }
  else if (month == 2) {
    return JulianLeap(year) ? 29 : 28;
  }
  else {
    return 31;
  }
}

uint JulianYearLength(uint year) {
  return JulianLeap(year) ? 366 : 365;
}

// Convert a Julian date to absolute:

uint j2a(Date date) {
  // The absolute date of Rosh Hashanah of year 1 is 2, which is 7 October -3760.
  // Since -3760 is a leap year, this is 281 days after 31 December -3761, the absolute date
  // of which would have been -279.
  int d = -279;
  // d is now the absolute date of 31 December -3761.
  int year;
  for (year=-3760; year<yearBound && year<date.year; year++) {
    d += JulianYearLength(year);
  }
  // d is now the absolute date of 31 December of year preceding date.year.
  uint month;
  for (month=1; month<=12 && month<date.month; month++) {
    d += JulianMonthLength(month, year);
  }
  // d is now the absolute date of the last day of month preceding date.month.
  return d + date.day;
}

// Convert an absolute date to Julian:

Date a2j(int d) {
  Date jdate;
  // Absolute date d is the (d + 279)th day from the beginning of -3759:
  d += 279;
  // The day of interest is now the dth day from the beginning of -3759:
  int year;
  for (year=-3760; year<yearBound && d>JulianYearLength(year); year++) {
    d -= JulianYearLength(year);
  }
  jdate.year = year;
  // The day of interest is now the dth day of year:
  uint month;
  for (month=1; month <= 12 && d>JulianMonthLength(month, year); month++) {
    d -= JulianMonthLength(month, year);
  }
  jdate.month = month;
  jdate.day = d;
  return jdate;
}
 
// Convert between Hebrew, Gregorian, and Julian dates:

Date h2j(Date date) {
  return a2j(h2a(date));
}

Date j2h(Date date) {
  return a2h(j2a(date));
}

Date g2j(Date date) {
  return a2j(g2a(date));
}

Date j2g(Date date) {
  return a2g(j2a(date));
}

// RAC end

string monthName(uint m, uint year) {
  switch (m) {
  case 1: return "Tishri";
  case 2: return "Cheshvan";
  case 3: return "Kislev";
  case 4: return "Tevat";
  case 5: return "Shevat";
  case 6: return leap(year) ? "Adar II" : "Adar";
  case 7: return "Nisan";
  case 8: return "Iyar";
  case 9: return "sivan";
  case 10: return "Tammuz";
  case 11: return "Av";
  case 12: return "Elul";
  case 13: return "Adar I";
  default: assert(false);
  }
}
	    
string GregorianMonthName(uint m) {
  switch (m) {
  case 1: return "January";
  case 2: return "February";
  case 3: return "March";
  case 4: return "April";
  case 5: return "May";
  case 6: return "June";
  case 7: return "July";
  case 8: return "August";
  case 9: return "September";
  case 10: return "October";
  case 11: return "November";
  case 12: return "December";
  default: assert(false);
  }
}
	    

int main() {

  uint num, d, m, y;
  Date gdate, hdate;

  while(true) {
    cout << endl << "Select one of the following:" << endl;
    cout << "  1 Convert Gregorian date to Hebrew" << endl;
    cout << "  2 Convert Hebrew date to Gregorian" << endl;
    cout << "  3 Convert absolute date to Hebrew" << endl;
    cout << "  4 Convert absolute date to Gregorian" << endl;
    cout << "  5 Convert Gregorian date to absolute" << endl;
    cout << "  6 Convert Hebrew date to absolute" << endl;
    cout << "  7 Terminate execution" << endl;
    cin >> num;

    switch (num) {
    case 1:
      cout << "Enter Gregorian date (d m y): ";
      cin >> d >> m >> y;
      gdate.day = d; gdate.month = m; gdate.year = y;
      hdate = g2h(gdate);
      cout << "Hebrew date: " << hdate.day << " " << monthName(hdate.month, hdate.year) << " " << hdate.year << endl;
      break;
    case 2:
      cout << "Enter Hebrew date (d m y): ";
      cin >> d >> m >> y;
      hdate.day = d; hdate.month = m; hdate.year = y;
      gdate = h2g(hdate);
      cout << "Gregorian date: " << gdate.day << " " << GregorianMonthName(gdate.month) << " " << gdate.year << endl;
      break;
    case 3:
      cout << "Enter absolute date: ";
      cin >> d;
      hdate = a2h(d);
      cout << "Hebrew date: " << hdate.day << " " << monthName(hdate.month, hdate.year) << " " << hdate.year << endl;
      break;    
    case 4:
      cout << "Enter absolute date: ";
      cin >> d;
      gdate = a2g(d);
      cout << "Hebrew date: " << gdate.day << " " << GregorianMonthName(gdate.month) << " " << gdate.year << endl;
      break;    
    case 5:
      cout << "Enter Gregorian date (d m y): ";
      cin >> d >> m >> y;
      gdate.day = d; gdate.month = m; gdate.year = y;
      d = g2a(gdate);
      cout << "Absolute date: " << d << endl;
      break;
    case 6:
      cout << "Enter Hebrew date (d m y): ";
      cin >> d >> m >> y;
      hdate.day = d; hdate.month = m; hdate.year = y;
      d = h2a(hdate);
      cout << "Absolute date: " << d << endl;
      break;
    default:
      return 0;
    }
  }
}
