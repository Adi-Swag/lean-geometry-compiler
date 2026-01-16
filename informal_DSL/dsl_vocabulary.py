# dsl_vocabulary.py

DSL_VOCABULARY = {
    "geometric_shapes": {
        "Point": "Point(A)",
        "Line": "Line(A,B)",
        "Segment": "Segment(A,B)",
        "Ray": "Ray(A,B)",
        "Angle": "Angle(A,B,C)",
        "Triangle": "Triangle(A,B,C)",
        "Quadrilateral": "Quadrilateral(A,B,C,D)",
        "Parallelogram": "Parallelogram(A,B,C,D)",
        "Square": "Square(A,B,C,D)",
        "Rectangle": "Rectangle(A,B,C,D)",
        "Rhombus": "Rhombus(A,B,C,D)",
        "Trapezoid": "Trapezoid(A,B,C,D)",
        "Kite": "Kite(A,B,C,D)",
        "Polygon": "Polygon(P)",
        "Pentagon": "Pentagon(A,B,C,D,E)",
        "Hexagon": "Hexagon(A,B,C,D,E,F)",
        "Heptagon": "Heptagon(A,B,C,D,E,F,G)",
        "Octagon": "Octagon(A,B,C,D,E,F,G,H)",
        "Circle": "Circle(O,r)",
        "Arc": "Arc(A,B,C)",
        "Sector": "Sector(O,A,B)",
        "Chord": "Chord(A,B)",
        "Semicircle": "Semicircle(O,A,B)",
        "CircularSegment": "CircularSegment(A,B)",
        "Ellipse": "Ellipse(E)",
        "Parabola": "Parabola(P)",
        "Hyperbola": "Hyperbola(H)",
        "Shape": "Shape(S)"
    },
    
    "unary_attributes": {
        # Angle classifications
        "RightAngle": "RightAngle(Angle(A,B,C))",
        "AcuteAngle": "AcuteAngle(Angle(A,B,C))",
        "ObtuseAngle": "ObtuseAngle(Angle(A,B,C))",
        "StraightAngle": "StraightAngle(Angle(A,B,C))",
        "ReflexAngle": "ReflexAngle(Angle(A,B,C))",
        
        # Triangle classifications
        "IsRight": "IsRight(Triangle(A,B,C))",
        "Isosceles": "Isosceles(Triangle(A,B,C))",
        "Equilateral": "Equilateral(Triangle(A,B,C))",
        
        # Polygon attributes
        "Regular": "Regular(Polygon(P))",
        "Convex": "Convex(Polygon(P))",
        "Concave": "Concave(Polygon(P))",
        
        # Colors
        "Red": "Red(Shape(S))",
        "Blue": "Blue(Shape(S))",
        "Green": "Green(Shape(S))",
        "Shaded": "Shaded(Shape(S))"
    },
    
    "measurements": {
        "AreaOf": "AreaOf(A)",
        "PerimeterOf": "PerimeterOf(P)",
        "RadiusOf": "RadiusOf(Circle(O,r))",
        "DiameterOf": "DiameterOf(Circle(O,r))",
        "CircumferenceOf": "CircumferenceOf(Circle(O,r))",
        "AltitudeOf": "AltitudeOf(A)",
        "HypotenuseOf": "HypotenuseOf(H)",
        "SideOf": "SideOf(S)",
        "WidthOf": "WidthOf(W)",
        "HeightOf": "HeightOf(H)",
        "LegOf": "LegOf(L)",
        "BaseOf": "BaseOf(B)",
        "MedianOf": "MedianOf(M)",
        "IntersectionOf": "IntersectionOf(A,B)",
        "MeasureOf": "MeasureOf(M)",
        "LengthOf": "LengthOf(L)",
        "ScaleFactorOf": "ScaleFactorOf(A,B)",
        "DistanceBetween": "DistanceBetween(Point(A),Point(B))",
        "AngleBetween": "AngleBetween(Line(A,B),Line(C,D))"
    },
    
    "binary_relations": {
        # Line-Point relations
        "PointLiesOnLine": "PointLiesOnLine(Point(A),Line(B,C))",
        "PointLiesOnCircle": "PointLiesOnCircle(Point(P),Circle(O,r))",
        "Between": "Between(Point(A),Point(B),Point(C))",
        "Collinear": "Collinear(Point(A),Point(B),Point(C))",
        
        # Line-Line relations
        "Parallel": "Parallel(Line(A,B),Line(C,D))",
        "Perpendicular": "Perpendicular(Line(A,B),Line(C,D))",
        "IntersectAt": "IntersectAt(Line(A,B),Line(C,D),Point(E))",
        "Concurrent": "Concurrent(Line(A,B),Line(C,D),Line(E,F),Point(G))",
        
        # Angle relations
        "BisectsAngle": "BisectsAngle(Line(A,B),Angle(C,D,E))",
        "CongruentAngle": "CongruentAngle(Angle(A,B,C),Angle(D,E,F))",
        "Complementary": "Complementary(Angle(A,B,C),Angle(D,E,F))",
        "Supplementary": "Supplementary(Angle(A,B,C),Angle(D,E,F))",
        "VerticalAngles": "VerticalAngles(Angle(A,B,C),Angle(D,E,F))",
        "AlternateInteriorAngles": "AlternateInteriorAngles(Angle(A,B,C),Angle(D,E,F))",
        "AlternateExteriorAngles": "AlternateExteriorAngles(Angle(A,B,C),Angle(D,E,F))",
        "CorrespondingAngles": "CorrespondingAngles(Angle(A,B,C),Angle(D,E,F))",
        "ConsecutiveInteriorAngles": "ConsecutiveInteriorAngles(Angle(A,B,C),Angle(D,E,F))",
        
        # Shape relations
        "Congruent": "Congruent(Polygon(P),Polygon(Q))",
        "Similar": "Similar(Polygon(P),Polygon(Q))",
        "CircumscribedTo": "CircumscribedTo(Shape(S),Shape(Q))",
        "InscribedIn": "InscribedIn(Shape(S),Shape(Q))",
        "Inside": "Inside(Point(A),Shape(S))",
        "Outside": "Outside(Point(A),Shape(Q))",
        "OnBoundary": "OnBoundary(Point(A),Shape(S))",
        "Touches": "Touches(Shape(P),Shape(Q))",
        "Overlaps": "Overlaps(Shape(P),Shape(Q))",
        
        # Circle-Line relations
        "Tangent": "Tangent(Line(A,B),Circle(O,r))",
        "Secant": "Secant(Line(A,B),Circle(O,r))"
    },
    
    "is_relations": {
        "IsMidpointOf": "IsMidpointOf(Point(A),Line(C,D))",
        "IsCentroidOf": "IsCentroidOf(Point(A),Shape(S))",
        "IsIncenterOf": "IsIncenterOf(Point(A),Shape(S))",
        "IsCircumcenterOf": "IsCircumcenterOf(Point(P),Triangle(A,B,C))",
        "IsOrthocenterOf": "IsOrthocenterOf(Point(P),Triangle(A,B,C))",
        "IsRadiusOf": "IsRadiusOf(Line(A,B),Circle(O,r))",
        "IsDiameterOf": "IsDiameterOf(Line(A,B),Circle(O,r))",
        "IsMidsegmentOf": "IsMidsegmentOf(Line(P,Q),Triangle(A,B,C))",
        "IsChordOf": "IsChordOf(Line(A,B),Circle(O,r))",
        "IsSideOf": "IsSideOf(Line(A,B),Polygon(P))",
        "IsHypotenuseOf": "IsHypotenuseOf(Line(A,B),Triangle(A,B,C))",
        "IsPerpendicularBisectorOf": "IsPerpendicularBisectorOf(Line(A,B),Triangle(A,B,C))",
        "IsAltitudeOf": "IsAltitudeOf(Line(A,B),Triangle(A,B,C))",
        "IsMedianOf": "IsMedianOf(Line(A,B),Quadrilateral(A,B,C,D))",
        "IsBaseOf": "IsBaseOf(Line(A,B),Quadrilateral(A,B,C,D))",
        "IsDiagonalOf": "IsDiagonalOf(Line(A,B),Quadrilateral(A,B,C,D))",
        "IsLegOf": "IsLegOf(Line(A,B),Trapezoid(A,B,C,D))"
    },
    
    "numerical_operators": {
        "SinOf": "SinOf(Var)",
        "CosOf": "CosOf(Var)",
        "TanOf": "TanOf(Var)",
        "CotOf": "CotOf(Var)",
        "SecOf": "SecOf(Var)",
        "CscOf": "CscOf(Var)",
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
        "Equals": "Equals(Var1,Var2)",
        "LessThan": "LessThan(Var1,Var2)",
        "GreaterThan": "GreaterThan(Var1,Var2)"
    },
    
    "construction_operations": {
        "Midpoint": "Midpoint(Point(A),Point(B))",
        "Intersection": "Intersection(Shape(S),Shape(T))",
        "Bisector": "Bisector(Angle(A,B,C))",
        "PerpendicularBisector": "PerpendicularBisector(Segment(A,B))",
        "ParallelThrough": "ParallelThrough(Line(A,B),Point(C))",
        "PerpendicularThrough": "PerpendicularThrough(Line(A,B),Point(C))"
    },
    
    "constants": {
        "Pi": "Pi",
        "E": "E",
        "GoldenRatio": "GoldenRatio"
    },
    
    "goals": {
        "Find": "Find(Var)",
        "Prove": "Prove(Proposition)",
        "UseTheorem": "UseTheorem(TheoremName)",
        "Calculate": "Calculate(Expression)",
        "Construct": "Construct(Object)"
    }
}

# Helper function to get all predicates by category
def get_predicates_by_category(category):
    """Returns all predicates in a given category."""
    return DSL_VOCABULARY.get(category, {})

# Helper function to get all predicates
def get_all_predicates():
    """Returns a flat dictionary of all predicates."""
    all_predicates = {}
    for category in DSL_VOCABULARY.values():
        all_predicates.update(category)
    return all_predicates

# Helper function to search for a predicate
def find_predicate(name):
    """Searches for a predicate by name across all categories."""
    for category, predicates in DSL_VOCABULARY.items():
        if name in predicates:
            return {
                "name": name,
                "syntax": predicates[name],
                "category": category
            }
    return None