import pytest
from python_ta.contracts import check_all_contracts


class Employee:
    """
    Represents an employee

    Representation Invariants:
    - len(self.name) > 0
    - self.wage >= 15
    """

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

    def __init__(self, name, wage, preferred_language):
        Employee.__init__(self, name, wage)
        self.preferred_language = preferred_language


class TeamMember:
    """
    Represents a person on a team

    Representation Invariants:
    - len(self.team) > 0
    """

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
check_all_contracts(__name__)


@pytest.fixture
def developer():
    return Developer("Ibrahim", 35, "Python")


@pytest.fixture
def teamlead():
    return TeamLead("David", 50, "Python", "PyTA")


def test_change_developer_wage_lower(developer) -> None:
    """
    Change the wage to a lower amount, expect an exception.
    """
    with pytest.raises(AssertionError) as excinfo:
        developer.change_wages(25)
    msg = str(excinfo.value)
    assert 'self.wage < new_wage' in msg


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
    assert 'self.wage >= 30' in msg


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
        teamlead.team = ''
    msg = str(excinfo.value)
    assert 'len(self.team) > 0' in msg
