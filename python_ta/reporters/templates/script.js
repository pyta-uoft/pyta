$("body").on("click", ".slider", function () {
    $(this).parent().next().toggleClass("hide-and-maintain-width");
    $(this).children().toggleClass("collapsed");
});
