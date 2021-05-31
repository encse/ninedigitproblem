#!/usr/bin/perl

use strict;

my(%used,@digits);

&uj_digit(1);
exit;

sub uj_digit {
 my $digits = shift(@_);
 foreach ('1','2','3','4','5','6','7','8','9') {
  if (! exists($used{$_})) {
     push(@digits,$_);
     my $number = join('',@digits);
     if ($number % $digits == 0) {
       if ($digits < 9) {
         $used{$_} = 'used';
         &uj_digit($digits+1);
         delete($used{$_});
       } else {
         print "$number\n";
       };
     };
     pop(@digits);
  };
 };
};
