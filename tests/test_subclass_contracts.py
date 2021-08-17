from typing import List

import pytest

from python_ta.contracts import check_all_contracts


class Employee:
    """
    Represents an employee

    Representation Invariants:
    - len(self.name) > 0
    - self.wage >= 15
    """

    name: str
    wage: float

    def __init__(self, name, wage):
        self.name = name
        self.wage = wage

    def change_wages(self, new_wage):
        """
        Precondition: self.wage < new_wage
        """
        self.wage = new_wage


class Developer(Employee):
    """
    Represents a sofware developer

    Representation Invariants:
    - self.preferred_language == "Python" or self.preferred_language == "Java"
    """

    preferred_language: str

    def __init__(self, name, wage, preferred_language):
        Employee.__init__(self, name, wage)
        self.preferred_language = preferred_language


class Teacher(Employee):
    """
    Represents a restaurant teacher

    Representation Invariants:
    - self.wage == self.wage_per_class * len(self.currently_teaching)
    """

    currently_teaching: List[str]
    wage_per_class: float

    def __init__(self, name, wage_per_class, currently_teaching):
        Employee.__init__(self, name, wage_per_class * len(currently_teaching))
        self.wage_per_class = wage_per_class
        self.currently_teaching = currently_teaching

    def teach_new_classes(self, currently_teaching):
        # temporary violation of Teacher rep invariant (if before/after lengths are different)
        self.change_wages(self.wage_per_class * len(currently_teaching))

        # amending violation
        self.currently_teaching = currently_teaching

    def update_wage_per_class(self, wage_per_class):
        # temporary violation of Teacher rep invariant (if wage rate different from before)
        self.wage_per_class = wage_per_class

        # amending violation
        self.change_wages(wage_per_class * len(self.currently_teaching))


class TeamMember:
    """
    Represents a person on a team

    Representation Invariants:
    - len(self.team) > 0
    """

    team: str

    def __init__(self, team):
        self.team = team


class TeamLead(Developer, TeamMember):
    """
    Represents a team lead

    Representation Invariants:
    - self.wage >= 30
    """

    def __init__(self, name, wage, preferred_language, team):
        Developer.__init__(self, name, wage, preferred_language)
        TeamMember.__init__(self, team)


# Decorating everything in this file
check_all_contracts(__name__, decorate_main=False)


@pytest.fixture
def developer():
    return Developer("Ibrahim", 35, "Python")


@pytest.fixture
def teamlead():
    return TeamLead("David", 50, "Python", "PyTA")


@pytest.fixture
def pe_bio_teacher():
    return Teacher("Jewel", 25, ["P.E.", "Biology"])


def test_change_developer_wage_lower(developer) -> None:
    """
    Change the wage to a lower amount, expect an exception.
    """
    with pytest.raises(AssertionError) as excinfo:
        developer.change_wages(25)
    msg = str(excinfo.value)
    assert "self.wage < new_wage" in msg


def test_increase_teamlead_wages(teamlead):
    """
    Increases the wages of the team lead.
    """
    teamlead.change_wages(75)
    assert teamlead.wage == 75


def test_decrease_teamlead_wages(teamlead):
    """
    Decrease the wages of the team lead to below 30. Expect an exception.
    """
    with pytest.raises(AssertionError) as excinfo:
        teamlead.wage = 20
    msg = str(excinfo.value)
    assert "self.wage >= 30" in msg


def test_change_teamlead_language(teamlead):
    """
    Change the preferred language to a wrong value. Expect an exception.
    """
    with pytest.raises(AssertionError) as excinfo:
        teamlead.preferred_language = "C++"
    msg = str(excinfo.value)
    assert 'self.preferred_language == "Python" or self.preferred_language == "Java"' in msg


def test_change_teamlead_name(teamlead):
    """
    Change the name of the teamlead.
    """
    teamlead.name = "Ignas"
    assert teamlead.name == "Ignas"


def test_change_teamlead_team_invalid(teamlead):
    """
    Changes the team of the teamlead to something invalid. Excpects an exception.
    """
    with pytest.raises(AssertionError) as excinfo:
        teamlead.team = ""
    msg = str(excinfo.value)
    assert "len(self.team) > 0" in msg


def test_call_super_when_temp_invalid(pe_bio_teacher):
    """
    Temporarily violates a rep invariant by setting an instance attribute but later remedies the
    violation by calling a method defined in the super class. Expects no exception.
    """
    pe_bio_teacher.update_wage_per_class(100)
    assert pe_bio_teacher.wage_per_class == 100
    assert pe_bio_teacher.wage == pe_bio_teacher.wage_per_class * len(
        pe_bio_teacher.currently_teaching
    )


def test_call_super_creates_temp_invalid(pe_bio_teacher):
    """
    Call an instance method that temporarily violates a rep invariant when calling a method
    defined in a super class but later remedies the violation. Expects no exception.
    """
    pe_bio_teacher.teach_new_classes(["Computer Science", "Video Production", "Life Science"])
    assert len(pe_bio_teacher.currently_teaching) == 3
    assert pe_bio_teacher.wage == pe_bio_teacher.wage_per_class * len(
        pe_bio_teacher.currently_teaching
    )
