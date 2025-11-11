# dsl_vocabulary.py

DSL_VOCABULARY = {
    "geometric_shapes": {
        "Point": "Point(A), Point($)",
        "Line": "Line(A,B), Line(m), Line($)",
        "Segment": "Segment(A,B), Segment($)",
        "Ray": "Ray(A,B), Ray($)",
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
        "Chord": "Chord(A,B), Chord($)",
        "Semicircle": "Semicircle(A,B), Semicircle($)",
        "CircularSegment": "CircularSegment(A,B), CircularSegment($)",
        "Ellipse": "Ellipse(A), Ellipse($)",
        "Parabola": "Parabola($)",
        "Hyperbola": "Hyperbola($)",
        "Shape": "Shape($)"
    },
    
    "unary_attributes": {
        # Angle classifications
        "RightAngle": "RightAngle(Angle($))",
        "AcuteAngle": "AcuteAngle(Angle($))",
        "ObtuseAngle": "ObtuseAngle(Angle($))",
        "StraightAngle": "StraightAngle(Angle($))",
        "ReflexAngle": "ReflexAngle(Angle($))",
        
        # Triangle classifications
        "Right": "Right(Triangle($))",
        "Isosceles": "Isosceles(Triangle($))",
        "Equilateral": "Equilateral(Triangle($))",
        "Scalene": "Scalene(Triangle($))",
        "Acute": "Acute(Triangle($))",
        "Obtuse": "Obtuse(Triangle($))",
        
        # Polygon attributes
        "Regular": "Regular(Polygon($))",
        "Convex": "Convex(Polygon($))",
        "Concave": "Concave(Polygon($))",
        
        # Colors
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
        "ScaleFactorOf": "ScaleFactorOf(A,B)",
        "DistanceBetween": "DistanceBetween(Point($),Point($))",
        "AngleBetween": "AngleBetween(Line($),Line($))"
    },
    
    "binary_relations": {
        # Line-Point relations
        "PointLiesOnLine": "PointLiesOnLine(Point($),Line($1,$2))",
        "PointLiesOnCircle": "PointLiesOnCircle(Point($),Circle($))",
        "Between": "Between(Point($),Point($),Point($))",
        "Collinear": "Collinear(Point($),Point($),Point($))",
        
        # Line-Line relations
        "Parallel": "Parallel(Line($),Line($))",
        "Perpendicular": "Perpendicular(Line($),Line($))",
        "IntersectAt": "IntersectAt(Line($),Line($),Point($))",
        "Concurrent": "Concurrent(Line($),Line($),Line($),Point($))",
        
        # Angle relations
        "BisectsAngle": "BisectsAngle(Line($),Angle($))",
        "CongruentAngle": "CongruentAngle(Angle($),Angle($))",
        "Complementary": "Complementary(Angle($),Angle($))",
        "Supplementary": "Supplementary(Angle($),Angle($))",
        "VerticalAngles": "VerticalAngles(Angle($),Angle($))",
        "AlternateInteriorAngles": "AlternateInteriorAngles(Angle($),Angle($))",
        "AlternateExteriorAngles": "AlternateExteriorAngles(Angle($),Angle($))",
        "CorrespondingAngles": "CorrespondingAngles(Angle($),Angle($))",
        "ConsecutiveInteriorAngles": "ConsecutiveInteriorAngles(Angle($),Angle($))",
        
        # Shape relations
        "Congruent": "Congruent(Polygon($),Polygon($))",
        "Similar": "Similar(Polygon($),Polygon($))",
        "CircumscribedTo": "CircumscribedTo(Shape($),Shape($))",
        "InscribedIn": "InscribedIn(Shape($),Shape($))",
        "Inside": "Inside(Point($),Shape($))",
        "Outside": "Outside(Point($),Shape($))",
        "OnBoundary": "OnBoundary(Point($),Shape($))",
        "Touches": "Touches(Shape($),Shape($))",
        "Overlaps": "Overlaps(Shape($),Shape($))",
        
        # Circle-Line relations
        "Tangent": "Tangent(Line($),Circle($))",
        "Secant": "Secant(Line($),Circle($))"
    },
    
    "is_relations": {
        "IsMidpointOf": "IsMidpointOf(Point($),Line($))",
        "IsCentroidOf": "IsCentroidOf(Point($),Shape($))",
        "IsIncenterOf": "IsIncenterOf(Point($),Shape($))",
        "IsCircumcenterOf": "IsCircumcenterOf(Point($),Triangle($))",
        "IsOrthocenterOf": "IsOrthocenterOf(Point($),Triangle($))",
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
        "Midpoint": "Midpoint(Point($),Point($))",
        "Intersection": "Intersection(Shape($),Shape($))",
        "Bisector": "Bisector(Angle($))",
        "PerpendicularBisector": "PerpendicularBisector(Segment($))",
        "ParallelThrough": "ParallelThrough(Line($),Point($))",
        "PerpendicularThrough": "PerpendicularThrough(Line($),Point($))"
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