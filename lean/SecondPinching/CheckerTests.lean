import SecondPinching.IntegerPositivity
open scoped Matrix
namespace SecondPinching

example : integerCertificateCheck 2 !![1, 0; 0, 1] !![1, 0; 0, 1] = true := by decide
example : integerCertificateCheck 2 !![-1, 0; 0, 1] !![1, 0; 0, 1] = false := by decide
example : integerCertificateCheck 2 !![1, 0; 0, 1] !![0, 0; 0, 1] = false := by decide
example : integerCertificateCheck 2 !![3, 1; 0, 3] !![1, 0; 0, 1] = false := by decide

end SecondPinching
