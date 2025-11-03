# dsl_vocabulary.py

DSL_VOCABULARY = {
    "geometric_shapes": {
        "Point": "Point(A), Point($)",
        "Line": "Line(A,B), Line(m), Line($)",
        "Angle": "Angle(A,B,C), Angle(A), Angle(1), Angle($)",
        "Triangle": "Triangle(A,B,C), Triangle($)",
        "Quadrilateral": "Quadrilateral(A,B,C,D), Quadrilateral($)",
        "Parallelogram": "Parallelogram(A,B,C,D), Parallelogram($)",
        "Square": "Square(A,B,C,D), Square($)",
        "Rectangle": "Rectangle(A,B,C,D), Rectangle($)",
        "Rhombus": "Rhombus(A,B,C,D), Rhombus($)",
        "Trapezoid": "Trapezoid(A,B,C,D), Trapezoid($)",
        "Kite": "Kite(A,B,C,D), Kite($)",
        "Polygon": "Polygon($)",
        "Pentagon": "Pentagon(A,B,C,D,E), Pentagon($)",
        "Hexagon": "Hexagon(A,B,C,D,E,F), Hexagon($)",
        "Heptagon": "Heptagon(A,B,C,D,E,F,G), Heptagon($)",
        "Octagon": "Octagon(A,B,C,D,E,F,G,H), Octagon($)",
        "Circle": "Circle(A), Circle(1), Circle($)",
        "Arc": "Arc(A,B), Arc(A,B,C), Arc($)",
        "Sector": "Sector(O,A,B), Sector($)",
        "Shape": "Shape($)"
    },
    
    "unary_attributes": {
        "RightAngle": "RightAngle(Angle($))",
        "Right": "Right(Triangle($))",
        "Isosceles": "Isosceles(Polygon($))",
        "Equilateral": "Equilateral(Polygon($))",
        "Regular": "Regular(Polygon($))",
        "Red": "Red(Shape($))",
        "Blue": "Blue(Shape($))",
        "Green": "Green(Shape($))",
        "Shaded": "Shaded(Shape($))"
    },
    
    "measurements": {
        "AreaOf": "AreaOf(A)",
        "PerimeterOf": "PerimeterOf(A)",
        "RadiusOf": "RadiusOf(A)",
        "DiameterOf": "DiameterOf(A)",
        "CircumferenceOf": "CircumferenceOf(A)",
        "AltitudeOf": "AltitudeOf(A)",
        "HypotenuseOf": "HypotenuseOf(A)",
        "SideOf": "SideOf(A)",
        "WidthOf": "WidthOf(A)",
        "HeightOf": "HeightOf(A)",
        "LegOf": "LegOf(A)",
        "BaseOf": "BaseOf(A)",
        "MedianOf": "MedianOf(A)",
        "IntersectionOf": "IntersectionOf(A,B)",
        "MeasureOf": "MeasureOf(A)",
        "LengthOf": "LengthOf(A)",
        "ScaleFactorOf": "ScaleFactorOf(A,B)"
    },
    
    "binary_relations": {
        "PointLiesOnLine": "PointLiesOnLine(Point($),Line($1,$2))",
        "PointLiesOnCircle": "PointLiesOnCircle(Point($),Circle($))",
        "Parallel": "Parallel(Line($),Line($))",
        "Perpendicular": "Perpendicular(Line($),Line($))",
        "IntersectAt": "IntersectAt(Line($),Line($),Point($))",
        "BisectsAngle": "BisectsAngle(Line($),Angle($))",
        "Congruent": "Congruent(Polygon($),Polygon($))",
        "Similar": "Similar(Polygon($),Polygon($))",
        "Tangent": "Tangent(Line($),Circle($))",
        "Secant": "Secant(Line($),Circle($))",
        "CircumscribedTo": "CircumscribedTo(Shape($),Shape($))",
        "InscribedIn": "InscribedIn(Shape($),Shape($))"
    },
    
    "is_relations": {
        "IsMidpointOf": "IsMidpointOf(Point($),Line($))",
        "IsCentroidOf": "IsCentroidOf(Point($),Shape($))",
        "IsIncenterOf": "IsIncenterOf(Point($),Shape($))",
        "IsRadiusOf": "IsRadiusOf(Line($),Circle($))",
        "IsDiameterOf": "IsDiameterOf(Line($),Circle($))",
        "IsMidsegmentOf": "IsMidsegmentOf(Line($),Triangle($))",
        "IsChordOf": "IsChordOf(Line($),Circle($))",
        "IsSideOf": "IsSideOf(Line($),Polygon($))",
        "IsHypotenuseOf": "IsHypotenuseOf(Line($),Triangle($))",
        "IsPerpendicularBisectorOf": "IsPerpendicularBisectorOf(Line($),Triangle($))",
        "IsAltitudeOf": "IsAltitudeOf(Line($),Triangle($))",
        "IsMedianOf": "IsMedianOf(Line($),Quadrilateral($))",
        "IsBaseOf": "IsBaseOf(Line($),Quadrilateral($))",
        "IsDiagonalOf": "IsDiagonalOf(Line($),Quadrilateral($))",
        "IsLegOf": "IsLegOf(Line($),Trapezoid($))"
    },
    
    "numerical_operators": {
        "SinOf": "SinOf(Var)",
        "CosOf": "CosOf(Var)",
        "TanOf": "TanOf(Var)",
        "CotOf": "CotOf(Var)",
        "HalfOf": "HalfOf(Var)",
        "SquareOf": "SquareOf(Var)",
        "SqrtOf": "SqrtOf(Var)",
        "RatioOf": "RatioOf(Var1,Var2)",
        "SumOf": "SumOf(Var1,Var2,...)",
        "AverageOf": "AverageOf(Var1,Var2,...)",
        "Add": "Add(Var1,Var2,...)",
        "Mul": "Mul(Var1,Var2,...)",
        "Sub": "Sub(Var1,Var2,...)",
        "Div": "Div(Var1,Var2,...)",
        "Pow": "Pow(Var1,Var2)",
        "Equals": "Equals(Var1,Var2)"
    },
    
    "goals": {
        "Find": "Find(Var)",
        "Prove": "Prove(Proposition)",
        "UseTheorem": "UseTheorem(TheoremName)"
    }
}

# Additional predicates I'm adding for better coverage
EXTENDED_PREDICATES = {
    "Segment": "Segment(A,B)",  # Line segment
    "Ray": "Ray(A,B)",  # Ray from A through B
    "Between": "Between(A,B,C)",  # Point B is between A and C
    "Collinear": "Collinear(A,B,C)",  # Three points on same line
    "CongruentAngle": "CongruentAngle(Angle($),Angle($))",  # Angle congruence
}