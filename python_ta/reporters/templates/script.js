$("body").on("click", ".slider", function () {
    $slider = $(this);
    //getting the next element
    $content = $slider.next();
    //open up the content needed - toggle the slide- if visible, slide up, if not slidedown.
    $content.slideToggle(500, function () {
        //execute this after slideToggle is done
        //change text of slider based on visibility of content div
        });

});
